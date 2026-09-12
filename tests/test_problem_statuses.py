"""Exercise status parsing and catalog promotion without changing permanent IDs."""

import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import update_catalog
from validate_problem_ids import REGISTRY, validate

CATEGORY = "randomized-and-low-rank-approximation"


class ProblemStatusTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def entry(self, identifier, status):
        path = self.root / CATEGORY / identifier / "README.md"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            f"# {identifier} — Original problem {identifier}\n\n"
            f"**Status:** {status}\n"
            "**Difficulty:** Medium\n"
            "**Importance:** High\n"
            "**Last checked:** 2026-09-11\n\n"
            "The original mathematical target remains here.\n",
            encoding="utf-8",
        )
        return path

    def test_read_problem_accepts_lean_verified(self):
        path = self.entry("RA-01", "Lean verified")
        self.assertEqual(update_catalog.read_problem(path), {
            "id": "RA-01",
            "title": "Original problem RA-01",
            "status": "Lean verified",
            "difficulty": "Medium",
            "importance": "High",
            "checked": "2026-09-11",
        })
        self.assertNotIn("Lean verified", update_catalog.OPEN)

    def test_read_problem_rejects_unknown_status(self):
        path = self.entry("RA-01", "Unrecognized status")
        with self.assertRaisesRegex(ValueError, "RA-01: unrecognized status 'Unrecognized status'"):
            update_catalog.read_problem(path)

    def test_promotion_preserves_counts_and_canonical_identity(self):
        entries = {
            "RA-01": self.entry("RA-01", "Open"),
            "RA-02": self.entry("RA-02", "Partially resolved"),
            "RA-03": self.entry("RA-03", "Solved"),
            "RA-04": self.entry("RA-04", "Solved"),
        }
        registry_path = self.root / REGISTRY
        registry_path.write_text(json.dumps({
            identifier: path.relative_to(self.root).as_posix()
            for identifier, path in entries.items()
        }), encoding="utf-8")
        (self.root / CATEGORY / "README.md").write_text("# Example category\n", encoding="utf-8")
        (self.root / "README.md").write_text(
            "# Example catalog\n\n<!-- catalog-summary -->\n<!-- /catalog-summary -->\n\n"
            "| Category | Problems |\n| --- | ---: |\n| Example category | 0 |\n",
            encoding="utf-8",
        )
        for args in [
            ("init", "-q"),
            ("add", "."),
            ("-c", "user.name=Status test", "-c", "user.email=status-test@example.invalid",
             "-c", "commit.gpgsign=false", "commit", "-qm", "Published entries"),
        ]:
            subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True)

        registry_before = registry_path.read_bytes()
        canonical_before = {identifier: path.read_bytes() for identifier, path in entries.items()}

        def regenerate():
            with patch.object(update_catalog, "ROOT", self.root), \
                    patch.object(update_catalog, "CATEGORIES", [CATEGORY]), \
                    patch.object(sys, "argv", ["update_catalog.py", "--base-ref", "HEAD"]), \
                    contextlib.redirect_stdout(io.StringIO()):
                update_catalog.main()
            return {
                name: (self.root / name).read_text(encoding="utf-8")
                for name in ["README.md", "CATALOG.md", f"{CATEGORY}/README.md"]
            }

        before = regenerate()
        promoted = entries["RA-03"]
        promoted.write_bytes(canonical_before["RA-03"].replace(b"**Status:** Solved", b"**Status:** Lean verified"))
        after = regenerate()

        summary = ("**2 problems with open targets:** 1 open and 1 partially resolved. "
                   "**2 other retained entries**, excluded from the open count.")
        evidence_before = "**Resolution evidence:** 2 solved (published or independently audited); 0 Lean verified."
        evidence_after = "**Resolution evidence:** 1 solved (published or independently audited); 1 Lean verified."
        for name in ["README.md", "CATALOG.md"]:
            with self.subTest(index=name):
                self.assertIn(summary, before[name])
                self.assertIn(summary, after[name])
                self.assertIn(evidence_before, before[name])
                self.assertIn(evidence_after, after[name])
        self.assertEqual(before["README.md"].replace(evidence_before, evidence_after), after["README.md"])
        for name, prefix in [("CATALOG.md", CATEGORY + "/"), (f"{CATEGORY}/README.md", "")]:
            with self.subTest(index=name):
                self.assertIn("**🏆 LEAN VERIFIED**", after[name])
                self.assertIn("**✅ SOLVED**", after[name])
                self.assertEqual(before[name].count("**✅ SOLVED**"), 2)
                self.assertEqual(after[name].count("**✅ SOLVED**"), 1)
                self.assertIn(f"[RA-03]({prefix}RA-03/README.md)", after[name])
                active, retained = after[name].split("Retained entries outside the open count", 1)
                self.assertNotIn("RA-03", active)
                self.assertIn("RA-03", retained)
        self.assertEqual(registry_before, registry_path.read_bytes())
        self.assertEqual(validate(self.root, "HEAD"), 4)
        for identifier, path in entries.items():
            expected = canonical_before[identifier]
            if identifier == "RA-03":
                expected = expected.replace(b"**Status:** Solved", b"**Status:** Lean verified")
            self.assertEqual(path.read_bytes(), expected)


if __name__ == "__main__":
    unittest.main()
