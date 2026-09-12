"""Exercise identity changes and historical registry protection using stdlib only."""

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
from validate_problem_ids import REGISTRY, discover, read_registry, validate

CATEGORY = "randomized-and-low-rank-approximation"
OTHER = "tensor-computations"


class PermanentIDTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.entry("RA-01")
        self.entry("RA-03")  # A published gap must not later be filled.
        self.registry()

    def entry(self, identifier, category=CATEGORY, heading=None):
        path = self.root / category / identifier / "README.md"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"# {heading or identifier} — Original problem\n\n**Status:** Open\n", encoding="utf-8")
        return path

    def registry(self):
        entries = discover([p.relative_to(self.root).as_posix() for p in self.root.glob("*/*/README.md")],
                           lambda p: (self.root / p).read_text())
        (self.root / REGISTRY).write_text(json.dumps(entries), encoding="utf-8")

    def history(self, with_registry=True):
        """Create disposable history only; never commit in the project checkout."""
        if not with_registry:
            (self.root / REGISTRY).unlink()
        self.git("init", "-q")
        self.git("add", ".")
        self.git("-c", "user.name=ID test", "-c", "user.email=id-test@example.invalid",
                 "-c", "commit.gpgsign=false", "commit", "-qm", "Published entries")
        if not with_registry:
            self.registry()

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.root), *args],
                              check=True, capture_output=True).stdout

    def test_current_registry_and_status_changes(self):
        path = self.root / CATEGORY / "RA-01" / "README.md"
        for status in ["Solved", "Lean verified", "Withdrawn", "Partially resolved"]:
            path.write_text(f"# RA-01 — Original problem\n\n**Status:** {status}\n")
            self.assertEqual(validate(self.root), 2)
        self.assertNotIn("Withdrawn", update_catalog.OPEN)
        self.assertIn("Withdrawn", update_catalog.STATUSES)

    def test_missing_registered_page(self):
        (self.root / CATEGORY / "RA-01" / "README.md").unlink()
        with self.assertRaisesRegex(ValueError, "Missing canonical README|missing registered entry"):
            validate(self.root)

    def test_unregistered_entry(self):
        self.entry("RA-04")
        with self.assertRaisesRegex(ValueError, "unregistered entry RA-04"):
            validate(self.root)

    def test_duplicate_heading_id(self):
        self.entry("RA-01", OTHER)
        with self.assertRaisesRegex(ValueError, "Duplicate problem ID RA-01"):
            validate(self.root)

    def test_heading_rename_and_malformed_ids(self):
        self.entry("RA-01", heading="RA-02")
        with self.assertRaisesRegex(ValueError, "directory and heading ID"):
            validate(self.root)
        for identifier in ["RA-00", "RA-1", "RA-001", "RA-010", "ra-01"]:
            with self.subTest(identifier=identifier), self.assertRaises(ValueError):
                read_registry(json.dumps({identifier: f"{CATEGORY}/{identifier}/README.md"}))

    def test_duplicate_json_keys(self):
        path = f"{CATEGORY}/RA-01/README.md"
        with self.assertRaisesRegex(ValueError, "Duplicate registry ID"):
            read_registry('{"RA-01": "' + path + '", "RA-01": "' + path + '"}')

    def test_paths_cannot_escape_or_alias(self):
        for path in [f"../{CATEGORY}/RA-01/README.md", f"{CATEGORY}//RA-01/README.md",
                     f"{CATEGORY}/RA-03/README.md", f"/{CATEGORY}/RA-01/README.md"]:
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, "invalid canonical path"):
                read_registry(json.dumps({"RA-01": path}))

    def test_symlinked_canonical_page(self):
        path = self.root / CATEGORY / "RA-01" / "README.md"
        target = self.root / "saved.md"
        path.rename(target)
        path.symlink_to(target)
        with self.assertRaisesRegex(ValueError, "must not be a symlink"):
            validate(self.root)

    def test_symlinked_registry(self):
        path = self.root / REGISTRY
        target = self.root / "saved.json"
        path.rename(target)
        path.symlink_to(target)
        with self.assertRaisesRegex(ValueError, "registry must not be a symlink"):
            validate(self.root)

    def test_append_only_and_large_suffixes(self):
        self.history()
        self.entry("RA-04")
        self.entry("RA-100")
        self.entry("ZZ-01")
        self.registry()
        self.assertEqual(validate(self.root, "HEAD"), 5)

    def test_cannot_fill_historical_gap(self):
        self.history()
        self.entry("RA-02")
        self.registry()
        with self.assertRaisesRegex(ValueError, "must exceed published RA-03"):
            validate(self.root, "HEAD")

    def test_cannot_remove_page_and_registry_record_together(self):
        self.history()
        (self.root / CATEGORY / "RA-01" / "README.md").unlink()
        (self.root / CATEGORY / "RA-01").rmdir()
        self.registry()
        with self.assertRaisesRegex(ValueError, "Published ID RA-01 must remain"):
            validate(self.root, "HEAD")

    def test_cannot_reassign_registered_path(self):
        self.history()
        old = self.root / CATEGORY / "RA-01" / "README.md"
        self.entry("RA-01", OTHER)
        old.unlink()
        old.parent.rmdir()
        self.registry()
        with self.assertRaisesRegex(ValueError, "Published ID RA-01 must remain"):
            validate(self.root, "HEAD")

    def test_first_registry_protects_already_published_ids(self):
        self.history(with_registry=False)
        self.assertEqual(validate(self.root, "HEAD"), 2)
        (self.root / CATEGORY / "RA-01" / "README.md").unlink()
        (self.root / CATEGORY / "RA-01").rmdir()
        self.entry("RA-04")
        self.registry()
        with self.assertRaisesRegex(ValueError, "Published ID RA-01 must remain"):
            validate(self.root, "HEAD")

    def test_invalid_base_is_not_silently_ignored(self):
        self.history()
        with self.assertRaises(ValueError):
            validate(self.root, "nonexistent-base")

    def test_committed_branch_renumber_detected_against_published_branch(self):
        self.history()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        old = self.root / CATEGORY / "RA-01" / "README.md"
        old.unlink()
        old.parent.rmdir()
        self.entry("RA-04")
        self.registry()
        self.git("add", ".")
        self.git("-c", "user.name=ID test", "-c", "user.email=id-test@example.invalid",
                 "-c", "commit.gpgsign=false", "commit", "-qm", "Bad numbering on a new branch")
        # A branch with an all-zero push 'before' must not validate only itself.
        self.assertEqual(validate(self.root, "HEAD"), 2)
        with self.assertRaisesRegex(ValueError, "Published ID RA-01 must remain"):
            validate(self.root, "refs/remotes/origin/main")

    def test_indexer_does_not_write_when_validation_fails(self):
        self.entry("RA-04")  # Deliberately not registered.
        index = self.root / "CATALOG.md"
        index.write_text("Keep this index untouched\n")
        before = {p.relative_to(self.root): p.read_bytes() for p in self.root.rglob("*") if p.is_file()}
        with patch.object(update_catalog, "ROOT", self.root), patch.object(sys, "argv", ["update_catalog.py"]):
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(ValueError, "unregistered"):
                update_catalog.main()
        after = {p.relative_to(self.root): p.read_bytes() for p in self.root.rglob("*") if p.is_file()}
        self.assertEqual(before, after)


if __name__ == "__main__":
    unittest.main()
