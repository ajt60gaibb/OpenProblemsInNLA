"""Regression checks for archive exclusion, scope gaps, and source provenance."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from statement_inventory import build_inventory, campaign_record, main, sha256


class StatementInventoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.canonical = "randomized-and-low-rank-approximation/RA-01/README.md"
        self.write(self.canonical, "# RA-01 — Exact original target\n\n**Status:** Solved\n")
        self.write("problem_ids.json", json.dumps({"RA-01": self.canonical}))
        self.git("init", "-q")
        self.git("add", ".")
        self.git("-c", "user.name=Inventory test", "-c", "user.email=inventory@example.invalid",
                 "-c", "commit.gpgsign=false", "commit", "-qm", "Published source")
        self.base = self.git("rev-parse", "HEAD").decode().strip()

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        return path

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True).stdout

    def inventory(self):
        return build_inventory(self.root, self.base)

    def test_review_and_verification_copies_do_not_count(self):
        prefix = "randomized-and-low-rank-approximation/RA-01/lean"
        for archive in ("reviews/old", "verification/source", "statement-history/frozen"):
            self.write(f"{prefix}/{archive}/Challenge.lean", "def Target : Prop := True\n")
        entry = self.inventory()["entries"][0]
        self.assertEqual(entry["classification"], "missing-statement")
        self.assertEqual(entry["local_sources"], {})

    def test_only_live_entry_point_imports_are_followed(self):
        prefix = "randomized-and-low-rank-approximation/RA-01/lean"
        self.write(f"{prefix}/Challenge.lean", "import NLA.RA01.Definitions\nimport Mathlib\n")
        self.write(f"{prefix}/NLA/RA01/Definitions.lean", "def Target : Prop := True\n")
        self.write(f"{prefix}/NLA/RA01/Unimported.lean", "def Unused : Prop := False\n")
        entry = self.inventory()["entries"][0]
        self.assertEqual(entry["classification"], "local-statement-source")
        self.assertEqual(len(entry["local_sources"]), 2)
        self.assertFalse(entry["solution_source_present"])
        self.assertEqual(entry["proof_verification"], "not-run-by-inventory")

    def test_published_source_hash_detects_changes_without_moving_base(self):
        old = self.inventory()["entries"][0]
        self.write(self.canonical, "# RA-01 — Altered target\n\n**Status:** Solved\n")
        changed = self.inventory()["entries"][0]
        self.assertNotEqual(old["canonical_sha256"], changed["canonical_sha256"])
        self.assertEqual(old["published_sha256"], changed["published_sha256"])
        self.assertFalse(changed["canonical_unchanged_from_base"])

    def test_unrelated_head_commit_does_not_change_inventory(self):
        old = self.inventory()
        self.write("unrelated.txt", "unrelated\n")
        self.git("add", "unrelated.txt")
        self.git("-c", "user.name=Inventory test", "-c", "user.email=inventory@example.invalid",
                 "-c", "commit.gpgsign=false", "commit", "-qm", "Unrelated change")
        self.assertEqual(old, self.inventory())

    def test_shared_metadata_is_not_itself_a_statement(self):
        readme_hash = sha256((self.root / self.canonical).read_bytes())
        record = {"id": "RA-01", "canonical_readme": self.canonical,
                  "source_sha256": readme_hash, "scope": "statement-only",
                  "module": "NLA.Statements.RA01", "declaration": "NLA.Statements.RA01.Target",
                  "lean_sha256": "missing", "reviews": [{"phase": "specification"}]}
        self.write("docs/lean/statements/RA-01/statement.json", json.dumps(record))
        entry = self.inventory()["entries"][0]
        self.assertEqual(entry["classification"], "missing-statement")
        self.assertIn("shared Lean source is missing", entry["campaign"]["metadata_issues"])
        source = self.write("lean-statements/NLA/Statements/RA01.lean", "def Target : Prop := True\n")
        entry = self.inventory()["entries"][0]
        self.assertEqual(entry["classification"], "shared-statement-source")
        self.assertIn("lean_sha256 does not match the shared source", entry["campaign"]["metadata_issues"])
        record["lean_sha256"] = sha256(source.read_bytes())
        self.write("docs/lean/statements/RA-01/statement.json", json.dumps(record))
        campaign = self.inventory()["entries"][0]["campaign"]
        self.assertEqual(campaign["metadata_issues"], [])
        self.assertEqual(campaign["fidelity_verdict"], "not-established-by-inventory")

    def test_scope_gap_does_not_become_proof_from_solution_file(self):
        path = "matrix-discrepancy-and-optimization/MD-06/README.md"
        self.write(path, "# MD-06 — Synchronization\n\n**Status:** Solved\n")
        self.write("problem_ids.json", json.dumps({"RA-01": self.canonical, "MD-06": path}))
        prefix = "matrix-discrepancy-and-optimization/MD-06/lean"
        self.write(f"{prefix}/Challenge.lean", "def Target : Prop := True\n")
        self.write(f"{prefix}/Solution.lean", "theorem placeholder : True := trivial\n")
        entry = next(e for e in self.inventory()["entries"] if e["id"] == "MD-06")
        self.assertEqual(entry["classification"], "local-scope-gap")
        self.assertTrue(entry["solution_source_present"])
        self.assertEqual(entry["completeness"], "known-scope-gap")
        self.assertTrue(entry["exactness_concerns"])

    def test_check_detects_stale_generated_outputs(self):
        argv = ["--root", str(self.root), "--base-ref", self.base]
        self.assertEqual(main(argv), 0)
        self.assertEqual(main(argv + ["--check"]), 0)
        self.write("docs/lean/statements/COVERAGE.md", "stale\n")
        self.assertEqual(main(argv + ["--check"]), 1)


if __name__ == "__main__":
    unittest.main()
