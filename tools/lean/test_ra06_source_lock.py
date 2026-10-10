"""Rejection controls for the RA-06 frozen full-target proof package."""

from pathlib import Path
import json
import shutil
import tempfile
import unittest

from harness import HarnessError, validate_project
from ra06_source_lock import validate_ra06_source_lock


SOURCE = Path(__file__).resolve().parents[2] / "randomized-and-low-rank-approximation/RA-06/lean"


class RA06SourceLockTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="nla-ra06-lock-")
        self.project = Path(self.temporary.name) / "lean"
        shutil.copytree(SOURCE, self.project, ignore=shutil.ignore_patterns(".lake"))

    def tearDown(self):
        self.temporary.cleanup()

    def test_exact_copied_closure_and_project_pass(self):
        validate_ra06_source_lock(self.project)
        self.assertEqual(validate_project(self.project)["theorem_names"], ["NLA.RA06.target"])

    def test_changed_module_fails(self):
        source = self.project / "NLA/Proofs/RA06/Final.lean"
        source.write_bytes(source.read_bytes() + b"\n")
        with self.assertRaisesRegex(ValueError, "frozen source changed"):
            validate_ra06_source_lock(self.project)

    def test_missing_or_extra_module_fails(self):
        source = self.project / "NLA/Proofs/RA06/Final.lean"
        source.unlink()
        with self.assertRaisesRegex(ValueError, "module set differs"):
            validate_ra06_source_lock(self.project)
        shutil.copyfile(SOURCE / "NLA/Proofs/RA06/Final.lean", source)
        (self.project / "NLA/Proofs/RA06/Extra.lean").write_text("import Mathlib\n")
        with self.assertRaisesRegex(ValueError, "module set differs"):
            validate_ra06_source_lock(self.project)

    def test_changed_lock_fails(self):
        lock = self.project / "ra06-source-lock.json"
        lock.write_bytes(lock.read_bytes() + b"\n")
        with self.assertRaisesRegex(ValueError, "source lock is absent or changed"):
            validate_ra06_source_lock(self.project)

    def test_missing_lock_and_modules_still_fails_harness(self):
        (self.project / "ra06-source-lock.json").unlink()
        shutil.rmtree(self.project / "NLA")
        with self.assertRaisesRegex(HarnessError, "source lock is absent or changed"):
            validate_project(self.project)

    def test_floating_mathlib_or_missing_leancert_fails(self):
        manifest_path = self.project / "lake-manifest.json"
        manifest = json.loads(manifest_path.read_text())
        for package in manifest["packages"]:
            if package["name"] == "mathlib":
                package["inputRev"] = "main"
        manifest_path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(HarnessError, "RA-06 Mathlib manifest"):
            validate_project(self.project)
        shutil.copyfile(SOURCE / "lake-manifest.json", manifest_path)
        manifest = json.loads(manifest_path.read_text())
        manifest["packages"] = [p for p in manifest["packages"] if p["name"] != "leancert"]
        manifest_path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(HarnessError, "RA-06 requires"):
            validate_project(self.project)


if __name__ == "__main__":
    unittest.main()
