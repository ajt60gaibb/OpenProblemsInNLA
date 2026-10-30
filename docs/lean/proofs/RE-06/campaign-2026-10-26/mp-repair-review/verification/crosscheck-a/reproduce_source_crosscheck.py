#!/usr/bin/env python3
"""Read immutable Git sources for scope-A mathematical assistance; no Lean replay."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

REF = "05ceb708f444ed36d34afe2eb1f2d98b0b059a0c"
ORIGINAL_A = "b8eb4d7d07dd4a682c81ba48f43ef93314fbc20b"
PREFIX = "docs/lean/proofs/RE-06/campaign-2026-10-26/"
GROUPS = ("pseudoinverse-author", "fullrank-author", "global-measurable-author")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    def blob(ref, path):
        return subprocess.check_output(["git", "show", f"{ref}:{path}"], cwd=args.repo)

    def sha(data):
        return hashlib.sha256(data).hexdigest()

    freezes = []
    unique = {}
    group_counts = {}
    for group in GROUPS:
        path = f"{PREFIX}{group}/SOURCE_FREEZE.json"
        raw = blob(REF, path)
        freeze = json.loads(raw)
        group_counts[group] = {"support_theorems": 0, "audit_theorems": 0,
                               "mathematical_modules": 0, "audit_modules": 0}
        assert freeze["whole_problem_verified"] is False
        assert freeze["original_model_and_statement_modified"] is False
        for entry in freeze["files"]:
            source = blob(REF, entry["path"])
            assert len(source) == entry["bytes"]
            assert sha(source) == entry["sha256"]
            assert source == blob(ORIGINAL_A, entry["path"])
            unique.setdefault(entry["path"], {"module": entry["module"],
                                             "sha256": sha(source), "bytes": len(source),
                                             "identical_to_original_A_epoch": True})
            if not entry["new_in_chunk"]:
                continue
            text = source.decode()
            namespace = re.findall(r"^namespace (\S+)", text, re.M)
            names = re.findall(r"^theorem\s+(\w+)", text, re.M)
            assert len(namespace) <= 1
            assert not names or len(namespace) == 1
            actual = [f"{namespace[0]}.{name}" for name in names]
            record = unique[entry["path"]]
            record["theorems"] = actual
            record["imports"] = re.findall(r"^import (\S+)", text, re.M)
            record["audit_module"] = entry["module"].endswith("Audit")
            key = "audit" if record["audit_module"] else "support"
            group_counts[group][f"{key}_theorems"] += len(actual)
            group_counts[group]["audit_modules" if record["audit_module"]
                                else "mathematical_modules"] += 1
            assert 'set_option leancert.trust "kernel"' in text
            # A bounded source check, not a substitute for parent compiler checks.
            code = re.sub(r"/\-.*?\-/", "", text, flags=re.S)
            code = re.sub(r"--[^\n]*", "", code)
            assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code)
        assert group_counts[group]["support_theorems"] == freeze["new_actual_support_theorems"]
        freezes.append({"path": path, "sha256": sha(raw), "bytes": len(raw)})

    assert [group_counts[g]["support_theorems"] for g in GROUPS] == [71, 9, 15]
    assert sum(c["mathematical_modules"] for c in group_counts.values()) == 18
    assert sum(c["audit_modules"] for c in group_counts.values()) == 3
    assert sum(c["audit_theorems"] for c in group_counts.values()) == 1
    assert len(unique) == 33
    result = {
        "reviewer": "/root/verification/mp_math_crosscheck",
        "scope": "Independent source-level mathematical assistance for scope A only",
        "git_commit": REF,
        "original_A_epoch": ORIGINAL_A,
        "freeze_files": freezes,
        "groups": group_counts,
        "unique_frozen_sources": unique,
        "support_theorems": 95,
        "audit_identity_theorems": 1,
        "fresh_Lean_outcomes_claimed_by_this_assistance": 0,
        "CI_or_Comparator_outcomes_claimed_by_this_assistance": 0,
        "rectangular_pseudoinverse_moment_verified": False,
        "full_success_or_Target_verified": False,
        "reproduction_script_sha256": sha(Path(__file__).read_bytes()),
    }
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "SOURCE_CHECKS.json").write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: 33 frozen sources; 95 support theorems plus one audit identity; original-A bytes unchanged.")


if __name__ == "__main__":
    main()
