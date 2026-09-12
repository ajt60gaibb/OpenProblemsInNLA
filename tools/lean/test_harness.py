#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Portable preflight tests; these do not replace the Linux checker probes."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import harness


class HarnessTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="nla-harness-test-")
        self.root = Path(self.temporary.name).resolve()
        self.project = self.root / "category/XX-01/lean"
        self.project.mkdir(parents=True)
        (self.project / "lakefile.toml").write_text('name = "Fixture"\n')
        (self.project / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
        self.manifest = {"packagesDir": ".lake/packages", "packages": []}
        self.config = {"challenge_module": "Challenge", "solution_module": "Solution",
                       "theorem_names": ["NlaFixture.checked"],
                       "permitted_axioms": sorted(harness.STANDARD_AXIOMS)}
        self.write()

    def tearDown(self):
        self.temporary.cleanup()

    def write(self):
        (self.project / "lake-manifest.json").write_text(json.dumps(self.manifest))
        (self.project / "comparator.json").write_text(json.dumps(self.config))

    def git(self, *args):
        env = harness.clean_environment()
        return subprocess.check_output(
            ["git", "-c", "user.name=Harness Fixture", "-c", "user.email=fixture@invalid", *args],
            cwd=self.root, env=env, stderr=subprocess.STDOUT)

    def commit_fixture(self):
        self.git("init", "-q")
        self.git("add", "category")
        self.git("commit", "-qm", "Commit verifier fixture")

    def test_real_source_lock(self):
        lock = harness.load_lock()
        self.assertEqual(lock["commit"], "8d1b0c0545a77b40245e84705aa7d273e6c81e62")
        self.assertEqual(len(lock["files"]), 58)

    def test_standard_config_and_stricter_axiom_subset(self):
        self.assertEqual(harness.validate_project(self.project), self.config)
        self.config["permitted_axioms"] = []
        self.write()
        harness.validate_project(self.project)

    def test_custom_sorry_and_native_axioms_are_rejected(self):
        for axiom in ["custom", "sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"]:
            with self.subTest(axiom=axiom):
                self.config["permitted_axioms"] = [axiom]
                self.write()
                with self.assertRaisesRegex(harness.HarnessError, "only propext"):
                    harness.validate_project(self.project)

    def test_duplicate_json_keys_are_rejected(self):
        (self.project / "comparator.json").write_text(
            '{"permitted_axioms": ["custom"], "permitted_axioms": []}')
        with self.assertRaisesRegex(harness.HarnessError, "duplicate JSON key"):
            harness.validate_project(self.project)

    def test_definition_holes_are_rejected(self):
        self.config["definition_names"] = ["resolveTheConjecture"]
        self.write()
        with self.assertRaisesRegex(harness.HarnessError, "definition holes"):
            harness.validate_project(self.project)

    def test_nonimmutable_or_credential_dependencies_are_rejected(self):
        valid = {"type": "git", "url": "https://github.com/leanprover-community/mathlib4",
                 "rev": "1" * 40}
        for change in [{"rev": "main"}, {"type": "path"},
                       {"url": "https://token@github.com/owner/repo"},
                       {"url": "git@github.com:owner/repo"}]:
            with self.subTest(change=change):
                self.manifest["packages"] = [{**valid, **change}]
                self.write()
                with self.assertRaisesRegex(harness.HarnessError, "immutable HTTPS"):
                    harness.validate_project(self.project)

    def test_same_module_and_empty_theorem_list_are_rejected(self):
        self.config["solution_module"] = "Challenge"
        self.write()
        with self.assertRaises(harness.HarnessError):
            harness.validate_project(self.project)
        self.config["solution_module"] = "Solution"
        self.config["theorem_names"] = []
        self.write()
        with self.assertRaises(harness.HarnessError):
            harness.validate_project(self.project)

    def test_mac_os_does_not_silently_fall_back(self):
        with patch("harness.platform.system", return_value="Darwin"):
            with self.assertRaisesRegex(harness.HarnessError, "fake-landrun is forbidden"):
                harness.linux_requirements()

    def test_snapshot_uses_committed_files_and_detects_change(self):
        self.commit_fixture()
        (self.project / "untracked.txt").write_text("not an input\n")
        fresh = self.root / "fresh"
        fresh.mkdir()
        provenance, hashes = harness.snapshot(self.project, fresh)
        self.assertEqual(provenance["project"], "category/XX-01/lean")
        self.assertFalse((fresh / "untracked.txt").exists())
        harness.unchanged(fresh, hashes)
        (fresh / "comparator.json").write_text("{}")
        with self.assertRaisesRegex(harness.HarnessError, "trusted input changed"):
            harness.unchanged(fresh, hashes)

    def test_uncommitted_trusted_file_is_rejected(self):
        self.commit_fixture()
        (self.project / "comparator.json").write_text("{}")
        with self.assertRaises(harness.HarnessError):
            harness.snapshot(self.project, self.root / "fresh")

    def test_tracked_compiled_artifact_is_rejected(self):
        (self.project / "Solution.olean").write_bytes(b"not a trusted input")
        self.commit_fixture()
        with self.assertRaisesRegex(harness.HarnessError, "tracked build artifact"):
            harness.snapshot(self.project, self.root / "fresh")


if __name__ == "__main__":
    unittest.main(verbosity=2)
