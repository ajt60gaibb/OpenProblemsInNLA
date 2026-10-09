"""Meaningful rejection controls for the MF-23 pinned source closure."""

from pathlib import Path
import shutil
import tempfile
import unittest

from upstream_source_lock import validate_mf23_source_lock


SOURCE = Path(__file__).resolve().parents[2] / "matrix-functions-and-stability/MF-23/lean"


class MF23SourceLockTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="nla-mf23-lock-")
        self.project = Path(self.temporary.name) / "lean"
        self.project.mkdir()
        shutil.copytree(SOURCE / "OAI", self.project / "OAI")
        for name in ("upstream-source-lock.json", "UPSTREAM-LICENSE.txt"):
            shutil.copyfile(SOURCE / name, self.project / name)

    def tearDown(self):
        self.temporary.cleanup()

    def test_exact_closure_passes(self):
        validate_mf23_source_lock(self.project)

    def test_changed_module_fails(self):
        model = self.project / "OAI/Analysis/DirectCrouzeix/Model.lean"
        model.write_bytes(model.read_bytes() + b"\n")
        with self.assertRaisesRegex(ValueError, "pinned source changed"):
            validate_mf23_source_lock(self.project)

    def test_missing_or_extra_module_fails(self):
        folder = self.project / "OAI/Analysis/DirectCrouzeix"
        (folder / "Model.lean").unlink()
        with self.assertRaisesRegex(ValueError, "module set differs"):
            validate_mf23_source_lock(self.project)
        shutil.copyfile(SOURCE / "OAI/Analysis/DirectCrouzeix/Model.lean",
                        folder / "Model.lean")
        (folder / "Extra.lean").write_text("import Mathlib\n")
        with self.assertRaisesRegex(ValueError, "module set differs"):
            validate_mf23_source_lock(self.project)

    def test_changed_lock_or_license_fails(self):
        lock = self.project / "upstream-source-lock.json"
        lock.write_bytes(lock.read_bytes() + b"\n")
        with self.assertRaisesRegex(ValueError, "source lock is absent or changed"):
            validate_mf23_source_lock(self.project)
        shutil.copyfile(SOURCE / "upstream-source-lock.json", lock)
        (self.project / "UPSTREAM-LICENSE.txt").write_text("changed\n")
        with self.assertRaisesRegex(ValueError, "license text changed"):
            validate_mf23_source_lock(self.project)


if __name__ == "__main__":
    unittest.main()
