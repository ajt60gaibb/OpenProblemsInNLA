"""Rejection controls for review binding and immutable statement boundaries."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("statement_check", Path(__file__).with_name("check.py"))
check = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(check)


class StatementGates(unittest.TestCase):
    def fixture(self, root):
        problem_id = "RA-01"
        canonical = "randomized/RA-01/README.md"
        specification = "docs/lean/statements/RA-01/NUMERICAL_TARGETS.md"
        files = {canonical: "Complete original problem\n",
                 "docs/lean/statements/RA-01/ORIGINAL.md": "Complete original problem\n",
                 specification: "Exact specification\n",
                 check.source_path(problem_id).as_posix(): "import NLA.Statements.Shared\nnamespace NLA.Statements.RA01\ndef Target : Prop := True\nend NLA.Statements.RA01\n",
                 "lean-statements/NLA/Statements/Shared.lean": "-- complete mathematical shared definitions\n",
                 "problem_ids.json": json.dumps({problem_id: canonical})}
        files.update({p.as_posix(): "pinned input\n" for p in check.PINS})
        for relative, content in files.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        check.freeze(root, problem_id)
        data = {"schema_version": 1, "id": problem_id, "scope": "statement-only",
                "canonical_readme": canonical, "source_sha256": check.digest(root / canonical),
                "specification": specification, "specification_sha256": check.digest(root / specification),
                "module": "NLA.Statements.RA01", "declaration": "NLA.Statements.RA01.Target",
                "lean_sha256": check.digest(root / check.source_path(problem_id)),
                "frozen_sha256": check.digest(root / check.frozen_path(problem_id)),
                "authors": ["author"], "reviews": []}
        for phase in ("specification", "lean-boundary"):
            for reviewer in ("first", "second"):
                report = f"docs/lean/statements/RA-01/{phase}-{reviewer}.md"
                (root / report).write_text("Independent review of specified files\n")
                data["reviews"].append({"reviewer": reviewer, "is_ai": True, "phase": phase,
                                        "verdict": "approve", "report_path": report,
                                        "report_sha256": check.digest(root / report),
                                        "input_sha256": {p: check.digest(root / p) for p in check.review_inputs(root, data, phase)}})
        path = root / "docs/lean/statements/RA-01/statement.json"
        path.write_text(json.dumps(data))
        return path, data

    def test_duplicate_json_key_rejected(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            json.loads('{"scope": "proof", "scope": "statement-only"}', object_pairs_hook=check.unique)

    def test_ids_preserve_registry_spelling(self):
        self.assertEqual(check.source_path("RA-100").name, "RA100.lean")
        for value in ("RA-1", "../RA-01", "ra-01"):
            with self.assertRaises(ValueError):
                check.source_path(value)

    def test_paths_cannot_escape_or_use_symlinks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "real").write_text("input")
            (root / "link").symlink_to(root / "real")
            for relative in ("../real", "/real", "link"):
                with self.assertRaises(ValueError):
                    check.contained(root, relative)

    def test_changed_input_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            source = root / "source"
            source.write_text("reviewed")
            sha = check.digest(source)
            check.check_hash(root, "source", sha)
            source.write_text("changed")
            with self.assertRaisesRegex(ValueError, "changed reviewed"):
                check.check_hash(root, "source", sha)

    def test_freeze_is_separate_and_cannot_silently_refresh(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            source = root / check.source_path("RA-01")
            source.parent.mkdir(parents=True)
            source.write_text("namespace NLA.Statements.RA01\ndef Target : Prop := True\nend NLA.Statements.RA01\n")
            check.freeze(root, "RA-01")
            frozen = root / check.frozen_path("RA-01")
            self.assertIn("namespace NLA.ReviewedStatements.RA01", frozen.read_text())
            self.assertNotIn("namespace NLA.ReviewedStatements.RA01", source.read_text())
            with self.assertRaisesRegex(ValueError, "already exists"):
                check.freeze(root, "RA-01")

    def test_identity_checks_actual_frozen_proposition_and_no_holes(self):
        files = check.identity_files([{"id": "RA-01", "module": "NLA.Statements.RA01",
                                      "declaration": "NLA.Statements.RA01.Target"}])
        self.assertIn("NLA.Statements.RA01.Target = NLA.ReviewedStatements.RA01.Target := by rfl", files["IdentitySolution.lean"])
        self.assertNotIn("sorry", files["IdentitySolution.lean"])
        self.assertEqual(json.loads(files["comparator.json"])["definition_names"], [])

    def test_generated_checks_include_all_direct_computation_controls_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            for relative in (
                "NLA/Computation/SVDControls.lean",
                "NLA/Computation/Controls.lean",
                "NLA/Computation/BandIntervalControls.lean",
                "NLA/Computation/OrdinaryMachine.lean",
                "NLA/Computation/Nested/HiddenControls.lean",
                "NLA/Statements/UnrelatedControls.lean",
                "OtherControls.lean",
            ):
                path = root / check.PACKAGE / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("-- fixture module\n")
            text = check.generated_checks(root, [])
            self.assertIn("import NLA\n", text)
            self.assertIn("import StatementControls\n", text)
            self.assertEqual(
                [line for line in text.splitlines() if line.startswith("import NLA.Computation.")],
                ["import NLA.Computation.BandIntervalControls",
                 "import NLA.Computation.Controls",
                 "import NLA.Computation.SVDControls"],
            )
            for excluded in ("OrdinaryMachine", "HiddenControls", "UnrelatedControls", "OtherControls"):
                self.assertNotIn(excluded, text)

    def test_computation_control_symlinks_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            source = root / "external.lean"
            source.write_text("-- not a retained local control\n")
            link = root / check.PACKAGE / "NLA/Computation/AliasControls.lean"
            link.parent.mkdir(parents=True)
            link.symlink_to(source)
            with self.assertRaisesRegex(ValueError, "symbolic links"):
                check.generated_checks(root, [])

    def test_complete_review_metadata_and_import_binding(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            path, data = self.fixture(root)
            check.validate_metadata(root, path)
            data["reviews"][2]["input_sha256"].pop("lean-statements/NLA/Statements/Shared.lean")
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "omits"):
                check.validate_metadata(root, path)

    def test_authors_cannot_review_own_statement(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            path, data = self.fixture(root)
            data["reviews"][0]["reviewer"] = "author"
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "independent"):
                check.validate_metadata(root, path)

    def test_complete_original_cannot_be_truncated(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            path, _ = self.fixture(root)
            (path.parent / "ORIGINAL.md").write_text("Only easy subquestion")
            with self.assertRaisesRegex(ValueError, "complete canonical"):
                check.validate_metadata(root, path)

    def test_two_approvals_required_for_each_phase(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            path, data = self.fixture(root)
            data["reviews"].pop()
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "two independent lean-boundary"):
                check.validate_metadata(root, path)

    def test_review_report_change_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            path, data = self.fixture(root)
            (root / data["reviews"][0]["report_path"]).write_text("Different verdict")
            with self.assertRaisesRegex(ValueError, "changed reviewed"):
                check.validate_metadata(root, path)

    def test_unsupported_import_forms_fail_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            source = root / check.source_path("RA-01")
            source.parent.mkdir(parents=True)
            for content in ["public import NLA.Statements.Shared\n", "private import NLA.Statements.Shared\n", "import\n NLA.Statements.Shared\n", "import NLA.Statements.Shared NLA.Other\n"]:
                source.write_text(content)
                with self.assertRaisesRegex(ValueError, "plain import"):
                    check.local_imports(root, check.source_path("RA-01"))

    def test_entire_record_removal_cannot_skip_base_check(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with patch.object(check.subprocess, "check_output", return_value="docs/lean/statements/RA-01/statement.json\0"):
                with self.assertRaisesRegex(ValueError, "missing input"):
                    check.require_retained(root, "published-base")


if __name__ == "__main__":
    unittest.main()
