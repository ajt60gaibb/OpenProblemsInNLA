"""Checks the MF-23 toolchain adaptation and exact LeanCert profile pin."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import harness


class MF23ProfileTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="nla-mf23-profile-")
        self.root = Path(self.temporary.name).resolve()

    def tearDown(self):
        self.temporary.cleanup()

    def test_exact_adapted_toolchains_and_unchanged_checker_sources(self):
        lock = harness.load_lock()
        entries = [e for e in lock["files"] if e["destination"] in harness.MF23_TOOLCHAIN_FILES]
        self.assertEqual({e["destination"] for e in entries}, harness.MF23_TOOLCHAIN_FILES)
        original = (lock["lean_toolchain"] + "\n").encode()
        adapted = (harness.MF23_TOOLCHAIN + "\n").encode()
        self.assertEqual(len(original), len(adapted))
        for entry in entries:
            self.assertEqual(hashlib.sha256(original).hexdigest(), entry["sha256"])
            path = self.root / entry["destination"]
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(adapted)
        checker = {"destination": ".tools/comparator/Comparator/Check.lean",
                   "bytes": len(b"pinned-checker"),
                   "sha256": hashlib.sha256(b"pinned-checker").hexdigest()}
        checker_path = self.root / checker["destination"]
        checker_path.parent.mkdir(parents=True, exist_ok=True)
        checker_path.write_bytes(b"pinned-checker")
        fixture = {"files": [*entries, checker]}
        harness.verify_sources(self.root, fixture, "mf23")
        # The MF-23 profile must reject a silently unadapted Lean 4.33.1 toolchain.
        (self.root / entries[0]["destination"]).write_bytes(original)
        with self.assertRaises(harness.HarnessError):
            harness.verify_sources(self.root, fixture, "mf23")
        (self.root / entries[0]["destination"]).write_bytes(adapted)
        checker_path.write_bytes(b"changed-source")
        with self.assertRaises(harness.HarnessError):
            harness.verify_sources(self.root, fixture, "mf23")

    def test_mf23_leancert_pin_does_not_accept_default_pin(self):
        project = self.root / "lean"
        project.mkdir()
        url = "https://github.com/alerad/leancert.git"
        revision = harness.MF23_LEANCERT_REV
        (project / "lakefile.toml").write_text(
            'name = "Fixture"\n[[require]]\nname = "leancert"\n'
            f'git = "{url}"\nrev = "{revision}"\n')
        manifest = {"packages": [{"name": "leancert", "url": url,
                                  "rev": revision, "inputRev": revision}]}
        (project / "lake-manifest.json").write_text(json.dumps(manifest))
        self.assertTrue(harness.pinned_leancert(project, "mf23"))
        self.assertRaises(harness.HarnessError, harness.pinned_leancert, project, "default")
        manifest["packages"][0]["rev"] = harness.LEANCERT_REV
        (project / "lake-manifest.json").write_text(json.dumps(manifest))
        self.assertRaises(harness.HarnessError, harness.pinned_leancert, project, "mf23")
        manifest["packages"] = []
        (project / "lake-manifest.json").write_text(json.dumps(manifest))
        self.assertRaises(harness.HarnessError, harness.pinned_leancert, project, "mf23")

    def test_mf23_profile_requires_source_lock_even_if_closure_deleted(self):
        project = self.root / "project"
        project.mkdir()
        (project / "lakefile.toml").write_text('name = "Fixture"\n')
        with self.assertRaisesRegex(harness.HarnessError, "source lock is absent"):
            harness.validate_project(project, "mf23")

    def test_mf23_mathlib_lakefile_and_manifest_pins(self):
        project = self.root / "lean"
        project.mkdir()
        url = "https://github.com/leanprover-community/mathlib4.git"
        revision = harness.MF23_MATHLIB_REV
        (project / "lakefile.toml").write_text(
            'name = "Fixture"\n[[require]]\nname = "mathlib"\n'
            f'git = "{url}"\nrev = "{revision}"\n')
        manifest = {"packages": [{"name": "mathlib", "url": url,
                                  "rev": revision, "inputRev": revision}]}
        harness.pinned_mf23_mathlib(project, manifest)
        manifest["packages"][0]["inputRev"] = "main"
        self.assertRaises(harness.HarnessError,
                          harness.pinned_mf23_mathlib, project, manifest)
        manifest["packages"][0]["inputRev"] = revision
        (project / "lakefile.toml").write_text(
            'name = "Fixture"\n[[require]]\nname = "mathlib"\n'
            f'git = "{url}"\nrev = "main"\n')
        self.assertRaises(harness.HarnessError,
                          harness.pinned_mf23_mathlib, project, manifest)


if __name__ == "__main__":
    unittest.main()
