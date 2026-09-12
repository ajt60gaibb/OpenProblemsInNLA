"""Regression checks for project selection and truthful metadata coverage."""
import importlib.util
import json
from pathlib import Path
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
