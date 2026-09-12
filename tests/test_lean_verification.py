"""Regression checks for project selection and truthful metadata coverage."""
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
import yaml
import jsonschema

ROOT = Path(__file__).resolve().parents[1]

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

projects = load("lean_projects", ROOT / "tools/lean/projects.py")
manifest = load("lean_manifest", ROOT / "tools/lean/validate_manifest.py")
SCHEMA = json.loads((ROOT / "docs/lean/schema/v0.4.schema.json").read_text())

class ProjectSelectionTests(unittest.TestCase):
    def setUp(self):
        self.projects = [{"id": "IE-19", "project": "linear/IE-19/lean"},
                         {"id": "MI-19", "project": "matrix/MI-19/lean"}]

    def test_problem_proof_change_selects_only_that_problem(self):
        self.assertEqual(projects.select(self.projects, ["matrix/MI-19/lean/Solution.lean"]),
                         [self.projects[1]])

    def test_canonical_statement_change_rechecks_its_project(self):
        self.assertEqual(projects.select(self.projects, ["linear/IE-19/README.md"]),
                         [self.projects[0]])

    def test_shared_checker_or_schema_change_rechecks_every_project(self):
        for change in ["tools/lean/harness.py", "docs/lean/schema/v0.4.schema.json",
                       ".github/workflows/lean-verification.yml", "problem_ids.json"]:
            self.assertEqual(projects.select(self.projects, [change]), self.projects)

    def test_unrelated_document_does_not_rebuild_proofs(self):
        self.assertEqual(projects.select(self.projects, ["README.md"]), [])

    def test_control_fixture_toolchain_does_not_rebuild_problem_projects(self):
        self.assertEqual(projects.select(self.projects, ["docs/lean/ci-toolchain/lean-toolchain"]), [])

    def test_discovery_uses_registry_and_detects_incomplete_project(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "problem_ids.json").write_text(json.dumps({
                "IE-19": "linear/IE-19/README.md", "MI-19": "matrix/MI-19/README.md"}))
            project = root / "linear/IE-19/lean"
            project.mkdir(parents=True)
            (project / "formalization.yaml").write_text("version: v0.4\n")
            self.assertEqual(projects.discover(root), [self.projects[0]])

    def test_invalid_registry_path_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "problem_ids.json").write_text('{"IE-19":"../outside/README.md"}')
            with self.assertRaises(ValueError):
                projects.discover(root)

    def test_source_only_project_cannot_skip_verification(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "problem_ids.json").write_text('{"IE-19":"linear/IE-19/README.md"}')
            project = root / "linear/IE-19/lean"
            project.mkdir(parents=True)
            (project / "Challenge.lean").write_text("-- incomplete source-only draft\n")
            self.assertEqual(projects.discover(root), [self.projects[0]])

    def test_symlinked_project_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "problem_ids.json").write_text('{"IE-19":"linear/IE-19/README.md"}')
            (root / "elsewhere").mkdir()
            project = root / "linear/IE-19/lean"
            project.parent.mkdir(parents=True)
            project.symlink_to(root / "elsewhere", target_is_directory=True)
            with self.assertRaises(ValueError):
                projects.discover(root)

class ProjectSelectionGitTests(unittest.TestCase):
    """Exercise the CLI against real base/head trees, including Git path quoting."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name) / "repo"
        self.root.mkdir()
        self.output = Path(self.temporary.name) / "github-output"
        self.git("init", "-q")
        registry = {"IE-19": "linear/IE-19/README.md",
                    "MI-19": "matrix/MI-19/README.md",
                    "MI-20": "matrix/MI-20/README.md"}
        (self.root / "problem_ids.json").write_text(json.dumps(registry))
        for identifier, canonical in registry.items():
            readme = self.root / canonical
            readme.parent.mkdir(parents=True)
            readme.write_text(f"# {identifier}\n\n**Status:** Lean verified\n")
            if identifier != "MI-20":
                project = readme.parent / "lean"
                project.mkdir()
                for name in ["Challenge.lean", "Solution.lean"]:
                    (project / name).write_text("-- source-presence fixture\n")
        self.commit("base fixture")
        self.base = self.git("rev-parse", "HEAD").strip()

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), *args],
                                       text=True, stderr=subprocess.STDOUT)

    def commit(self, message):
        self.git("add", "-A")
        self.git("-c", "user.name=Lean selector test", "-c", "user.email=test@localhost",
                 "commit", "-qm", message)

    def run_selection(self, base=None):
        self.output.write_text("")
        return subprocess.run(
            [sys.executable, str(ROOT / "tools/lean/projects.py"), "--root", str(self.root),
             "--base-ref", base or self.base, "--github-output", str(self.output)],
            text=True, capture_output=True)

    def selected_ids(self, result):
        self.assertEqual(result.returncode, 0, result.stderr)
        return [entry["id"] for entry in json.loads(result.stdout)["include"]]

    def run_tools_changed(self, base=None):
        workflow = yaml.safe_load((ROOT / ".github/workflows/lean-verification.yml").read_text())
        step = next(step for step in workflow["jobs"]["select"]["steps"]
                    if step.get("id") == "projects")
        detector = re.search(r"<<'PY'\n(.*?)\nPY(?:\n|$)", step["run"], re.S)
        self.assertIsNotNone(detector, "workflow must retain its inline shared-tool detector")
        self.output.write_text("")
        result = subprocess.run([sys.executable, "-", base or self.base, str(self.output)],
                                input=detector.group(1), cwd=self.root,
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        return self.output.read_text()

    def test_unicode_quoted_and_newline_filenames_select_project(self):
        for name in ["Δ.lean", 'quoted"name.lean', "line\nbreak.lean"]:
            with self.subTest(name=name):
                base = self.git("rev-parse", "HEAD").strip()
                (self.root / "linear/IE-19/lean" / name).write_text("-- changed proof input\n")
                self.commit("proof input with special filename")
                self.assertEqual(self.selected_ids(self.run_selection(base)), ["IE-19"])

    def test_complete_project_deletion_fails_selection(self):
        shutil.rmtree(self.root / "linear/IE-19/lean")
        self.commit("remove project while retaining its canonical page")
        result = self.run_selection()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("linear/IE-19/lean", result.stderr)
        self.assertIn("removed or renamed", result.stderr)
        self.assertEqual(self.output.read_text(), "")

    def test_complete_project_rename_fails_selection(self):
        (self.root / "linear/IE-19/lean").rename(self.root / "linear/IE-19/lean-archive")
        self.commit("rename project away from its registered location")
        result = self.run_selection()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("linear/IE-19/lean", result.stderr)
        self.assertIn("removed or renamed", result.stderr)
        self.assertEqual(self.output.read_text(), "")

    def test_partial_project_deletion_still_selects_project(self):
        (self.root / "linear/IE-19/lean/Solution.lean").unlink()
        self.commit("remove one proof input")
        self.assertEqual(self.selected_ids(self.run_selection()), ["IE-19"])

    def test_renamed_file_selects_both_surviving_projects(self):
        (self.root / "linear/IE-19/lean/Solution.lean").rename(
            self.root / "matrix/MI-19/lean/Moved.lean")
        self.commit("move a proof input between projects")
        self.assertEqual(self.selected_ids(self.run_selection()), ["IE-19", "MI-19"])

    def test_new_source_only_project_for_existing_id_is_selected(self):
        project = self.root / "matrix/MI-20/lean"
        project.mkdir()
        (project / "Draft.lean").write_text("-- incomplete new formalization\n")
        self.commit("add source-only project")
        self.assertEqual(self.selected_ids(self.run_selection()), ["MI-20"])

    def test_workflow_unicode_quoted_newline_tool_changes_request_controls(self):
        directory = self.root / "tools/lean"
        directory.mkdir(parents=True)
        for name in ["Δ.py", 'quoted"name.py', "line\nbreak.py"]:
            with self.subTest(name=name):
                base = self.git("rev-parse", "HEAD").strip()
                (directory / name).write_text("# shared control fixture\n")
                self.commit("shared tool with special filename")
                self.assertEqual(self.run_tools_changed(base), "tools_changed=true\n")

    def test_workflow_renamed_away_tool_requests_controls(self):
        tool = self.root / "tools/lean/helper.py"
        tool.parent.mkdir(parents=True)
        tool.write_text("# identical contents for rename detection\n")
        self.commit("shared tool before rename")
        base = self.git("rev-parse", "HEAD").strip()
        archive = self.root / "archive/helper.py"
        archive.parent.mkdir()
        tool.rename(archive)
        self.commit("rename shared tool outside control directory")
        self.assertEqual(self.run_tools_changed(base), "tools_changed=true\n")

    def test_workflow_control_fixture_toolchain_requests_only_controls(self):
        pin = self.root / "docs/lean/ci-toolchain/lean-toolchain"
        pin.parent.mkdir(parents=True)
        pin.write_text("control fixture toolchain\n")
        self.commit("control fixture pin change")
        self.assertEqual(self.run_tools_changed(), "tools_changed=true\n")
        self.assertEqual(self.selected_ids(self.run_selection()), [])


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "Solution.lean").write_text("-- source-presence fixture, not a proof\n")
        self.config = {"challenge_module": "Challenge", "solution_module": "Solution",
                       "theorem_names": ["NLA.Test.result"], "definition_names": [],
                       "permitted_axioms": sorted(manifest.ALLOWED_AXIOMS)}
        self.metadata = {
            "version": "v0.4",
            "project": {"name": "Fixture", "authors": ["Test author"], "license": "Apache-2.0"},
            "sources": [{"title": "Test source", "type": "original-proof"}],
            "automation": {"methods": [{"method": "manual"}]},
            "review": {"status": "unchecked"},
            "status": {"sorry_count": 0, "sorry_in_definitions": 0, "axioms": [],
                       "main_results": [{"declaration": "NLA.Test.result", "file": "Solution.lean",
                                         "sorry_count": 0, "axioms": [],
                                         "comparator_config": "comparator.json"}]}}

    def run_check(self):
        (self.root / "formalization.yaml").write_text(yaml.safe_dump(self.metadata))
        (self.root / "comparator.json").write_text(json.dumps(self.config))
        manifest.validate(self.root, SCHEMA)

    def test_valid_consistent_metadata(self):
        self.run_check()

    def test_duplicate_yaml_status_is_rejected(self):
        (self.root / "formalization.yaml").write_text(
            "status:\n  sorry_count: 1\n" + yaml.safe_dump(self.metadata))
        (self.root / "comparator.json").write_text(json.dumps(self.config))
        with self.assertRaisesRegex(ValueError, "Duplicate.*status"):
            manifest.validate(self.root, SCHEMA)

    def test_duplicate_nested_yaml_key_is_rejected(self):
        (self.root / "formalization.yaml").write_text(
            yaml.safe_dump(self.metadata).replace("sorry_count: 0", "sorry_count: 1\n  sorry_count: 0", 1))
        (self.root / "comparator.json").write_text(json.dumps(self.config))
        with self.assertRaisesRegex(ValueError, "Duplicate.*sorry_count"):
            manifest.validate(self.root, SCHEMA)

    def test_duplicate_comparator_key_is_rejected(self):
        (self.root / "formalization.yaml").write_text(yaml.safe_dump(self.metadata))
        (self.root / "comparator.json").write_text(
            '{"permitted_axioms":["sorryAx"],' + json.dumps(self.config)[1:])
        with self.assertRaisesRegex(ValueError, "Duplicate.*permitted_axioms"):
            manifest.validate(self.root, SCHEMA)

    def test_missing_required_schema_field(self):
        del self.metadata["sources"]
        with self.assertRaises(jsonschema.ValidationError): self.run_check()

    def test_unchecked_export_is_rejected(self):
        self.metadata["status"]["main_results"].append({
            "declaration": "NLA.Test.unchecked", "file": "Solution.lean", "sorry_count": 0,
            "axioms": [], "comparator_config": "comparator.json"})
        with self.assertRaises(ValueError): self.run_check()

    def test_empty_theorem_list_is_rejected(self):
        self.config["theorem_names"] = []
        with self.assertRaises(ValueError): self.run_check()

    def test_custom_or_native_trust_is_rejected(self):
        for axiom in ["sorryAx", "Lean.ofReduceBool", "NLA.secretAx"]:
            self.config["permitted_axioms"] = [axiom]
            with self.assertRaises(ValueError): self.run_check()

    def test_nonzero_proof_sorries_rejected(self):
        self.metadata["status"]["sorry_count"] = 1
        with self.assertRaises(ValueError): self.run_check()

    def test_definition_hole_rejected(self):
        self.config["definition_names"] = ["NLA.Test.meaning"]
        with self.assertRaises(ValueError): self.run_check()

    def test_result_source_outside_project_rejected(self):
        self.metadata["status"]["main_results"][0]["file"] = "../other/Solution.lean"
        with self.assertRaises(ValueError): self.run_check()

    def test_result_specific_unchecked_axiom_rejected(self):
        self.metadata["status"]["main_results"][0]["axioms"] = ["NLA.assumeTarget"]
        with self.assertRaises(ValueError): self.run_check()

if __name__ == "__main__":
    unittest.main()
