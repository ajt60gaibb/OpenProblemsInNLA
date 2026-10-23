#!/usr/bin/env python3
"""Read-only audit of newly fetched complete candidates and actual CI inputs.

Checks retained original archives against live GitHub artifact metadata saved
beside this script. Does not execute Lean, CI, or the Linux strict replay tool.
"""
from collections import Counter
from functools import lru_cache
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import zipfile

OUT = Path(__file__).resolve().parent
ROOT = next(p for p in OUT.parents if (p / ".git").exists())
MAIN = "5487945e5a72abd952b0c89915915de8cc9b3e65"
INTEGRATION = "42d1665800d0185581149ef494e03055b533d636"
TR06 = "fa48059568762742b07f124c0e6ff65ef2ca212d"
CASES = {
    "SP-12": {
        "head": "d250bd50d602ec7fd6e55bb4fd19494c5e19b045", "pr": 362,
        "project": "eigenvalues-and-inverse-problems/SP-12/lean",
        "checked": "a7adfc8e30ad284f42ec2ea0221a990ee9804031",
        "run": 39149417211, "job": 117739903353, "artifact": 12143944681,
        "evidence": "docs/lean/proofs/SP-12/verification/refreshed-linux-ci",
        "zip": "lean-SP-12.zip", "result_dir": "verify-20261018T172559Z-4168",
        "review": "docs/lean/proofs/SP-12/verification/refreshed-linux-artifact-check.json",
        "source_review": "docs/lean/proofs/SP-12/CANONICAL_CLOSURE_REVIEW_2_2026-10-18.md",
        "inputs": 96, "lean_inputs": 55, "controls": 40,
    },
    "TR-14": {
        "head": "d6b233b488c168da5496fa9cbd14929e79fa788e", "pr": 363,
        "project": "tensor-computations/TR-14/lean",
        "checked": "16a1150d81f606ed6a8333be8c04730e0a477525",
        "run": 39174291223, "job": 117814377068, "artifact": 12154172015,
        "evidence": "docs/lean/proofs/TR-14/verification/promotion-linux-ci/16a1150d",
        "zip": "artifact.zip", "result_dir": "verify-20261018T230257Z-4178",
        "review": "docs/lean/proofs/TR-14/verification/promotion-linux-ci/16a1150d/independent-review-3.json",
        "source_review": "docs/lean/proofs/TR-14/FULL_TARGET_INDEPENDENT_REVIEW_3_2026-10-18.md",
        "inputs": 139, "lean_inputs": 82, "controls": 41,
    },
    "PF-05": {
        "head": "c4c7be592c51c8ba81d1579082813310a22b356d", "pr": 364,
        "project": "nonnegative-and-positive-factorizations/PF-05/lean",
        "checked": "c4c7be592c51c8ba81d1579082813310a22b356d",
        "run": 39176870923, "job": 117821318204, "artifact": 12154394713,
        "evidence": "docs/lean/proofs/PF-05/verification/promotion-linux-ci/c4c7be59",
        "zip": "original-artifact.zip", "result_dir": "verify-20261018T233305Z-4084",
        "review": "docs/lean/proofs/PF-05/verification/promotion-linux-ci/c4c7be59/independent-review-2026-10-23.json",
        "source_review": "docs/lean/proofs/PF-05/CANONICAL_FULL_TARGET_INDEPENDENT_REVIEW_3_2026-10-18.md",
        "inputs": 90, "lean_inputs": 46, "controls": 41,
    },
}


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


@lru_cache(None)
def read(ref, path):
    return git("show", f"{ref}:{path}")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def tree(ref, prefix):
    return git("ls-tree", "-r", "--name-only", ref, prefix).decode().splitlines()


def status(ref, path):
    return re.search(r"^\*\*Status:\*\*\s*(.*)$", read(ref, path).decode(), re.M).group(1).strip()


live = json.loads((OUT / "live-workflow-evidence.json").read_text())["runs"]
prs = json.loads((OUT / "live-pr-info.json").read_text())["prs"]
registry = json.loads(read(MAIN, "problem_ids.json"))
assert json.loads(read(INTEGRATION, "problem_ids.json")) == registry
reports = []
for ident, case in CASES.items():
    project = case["project"]
    compact = ident.replace("-", "")
    assert json.loads(read(case["head"], "problem_ids.json")) == registry
    assert status(MAIN, registry[ident]) == "Solved"
    assert status(INTEGRATION, registry[ident]) == "Lean verified"
    assert status(case["head"], registry[ident]) == "Lean verified"
    source_paths = {
        "live_statement": f"NLA/Statements/{compact}.lean",
        "frozen_statement": f"Reviewed/{compact}.lean",
        "original": "ORIGINAL.md", "specification": "NUMERICAL_TARGETS.md",
        "solution": "Solution.lean", "identity": "Identity.lean",
        "comparator": "comparator.json", "final": f"NLA/Proofs/{compact}/Final.lean",
    }
    assert read(INTEGRATION, f"{project}/{source_paths['live_statement']}") == read(MAIN, f"lean-statements/NLA/Statements/{compact}.lean")
    assert read(INTEGRATION, f"{project}/{source_paths['frozen_statement']}") == read(MAIN, f"lean-statements/Reviewed/{compact}.lean")
    assert read(INTEGRATION, f"{project}/ORIGINAL.md") == read(MAIN, registry[ident])
    assert read(INTEGRATION, f"{project}/NUMERICAL_TARGETS.md") == read(MAIN, f"docs/lean/statements/{ident}/NUMERICAL_TARGETS.md")
    solution = read(INTEGRATION, f"{project}/Solution.lean").decode()
    assert f"theorem target : NLA.Statements.{compact}.Target" in solution
    assert f"exact NLA.Proofs.{compact}.target" in solution
    assert "import Challenge" not in solution
    config = json.loads(read(INTEGRATION, f"{project}/comparator.json"))
    assert config["theorem_names"] == [f"NLA.{compact}.target"]
    assert config["definition_names"] == []
    assert set(config["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
    api = live[str(case["run"])]
    jobs = api["jobs"]["value"]["structuredContent"]["jobs"]
    job = next(j for j in jobs if j["id"] == case["job"])
    assert job["status"] == "completed" and job["conclusion"] == "success"
    artifacts = api["artifacts"]["value"]["structuredContent"]["artifacts"]
    artifact = next(a for a in artifacts if a["id"] == case["artifact"])
    assert not artifact["expired"] and artifact["workflow_run"]["head_sha"] == case["checked"]
    archive_data = read(INTEGRATION, f"{case['evidence']}/{case['zip']}")
    assert artifact["digest"] == "sha256:" + sha(archive_data)
    archive_members = []
    with zipfile.ZipFile(io.BytesIO(archive_data)) as archive:
        for member in archive.infolist():
            if member.is_dir():
                continue
            data = archive.read(member)
            assert data == read(INTEGRATION, f"{case['evidence']}/artifact/{member.filename}")
            archive_members.append({"path": member.filename, "sha256": sha(data)})
    result_path = f"{case['evidence']}/artifact/{case['result_dir']}/result.json"
    result_data = read(INTEGRATION, result_path)
    result = json.loads(result_data)
    assert result["repository_commit"] == case["checked"] and result["project"] == project
    assert result["result"] == "comparator-accepted" and result["lean_cert_proof_trust"] == "kernel-checked"
    assert result["config"] == config
    expected = result["input_sha256"]
    assert len(expected) == case["inputs"]
    assert sum(p.endswith(".lean") for p in expected) == case["lean_inputs"]
    source_files = {p.removeprefix(project + "/") for p in tree(INTEGRATION, project)}
    assert source_files == set(expected)
    inputs = []
    for relative, expected_sha in expected.items():
        current = read(INTEGRATION, f"{project}/{relative}")
        checked = read(case["checked"], f"{project}/{relative}")
        candidate = read(case["head"], f"{project}/{relative}")
        assert sha(current) == expected_sha and current == checked == candidate
        inputs.append({"path": relative, "sha256": expected_sha})
    retained_review_data = read(INTEGRATION, case["review"])
    retained_review = json.loads(retained_review_data)
    assert retained_review["passed"] and len(retained_review["checks"]) == case["controls"]
    assert all(c["passed"] for c in retained_review["checks"])
    assert retained_review["archive_sha256"] == sha(archive_data)
    pr = prs[str(case["pr"])]["value"]["structuredContent"]
    assert pr["state"] == "closed" and pr["merged"]
    reports.append({
        "id": ident, "candidate_head": case["head"], "integration_commit": INTEGRATION,
        "pr": {k: pr[k] for k in ["number", "url", "state", "merged", "base", "head", "head_sha", "merge_commit_sha"]},
        "canonical_status_on_main": "Solved", "canonical_status_on_integration": "Lean verified",
        "registered_id_path_and_original_and_frozen_statement_preserved": True,
        "full_target_export_without_added_hypotheses": f"NLA.{compact}.target : NLA.Statements.{compact}.Target",
        "core_input_hashes": {k: sha(read(INTEGRATION, f"{project}/{p}")) for k, p in source_paths.items()},
        "source_review": {"path": case["source_review"], "sha256": sha(read(INTEGRATION, case["source_review"]))},
        "live_successful_job": job, "live_artifact": artifact,
        "retained_archive_sha256_matches_live_github": sha(archive_data),
        "all_retained_archive_members_equal": archive_members,
        "retained_result": {"path": result_path, "sha256": sha(result_data), "result": result["result"], "lean_cert_proof_trust": result["lean_cert_proof_trust"]},
        "all_current_and_candidate_and_checked_commit_input_hashes_equal": inputs,
        "retained_independent_strict_replay": {"path": case["review"], "sha256": sha(retained_review_data), "passing_controls": case["controls"]},
        "new_lean_or_linux_or_strict_checker_execution_in_this_audit": False,
        "completion_gate_classification": "Complete reviewed full Target with exact current-package real Linux Comparator and LeanCert kernel receipt; reuse and integrate, no new proof implementation needed.",
    })

integration_statuses = {ident: status(INTEGRATION, path) for ident, path in registry.items()}
tr06_support = tree(TR06, "lean-statements/NLA/Proofs/TR06")
tr06_scope = json.loads(read(TR06, "docs/lean/proofs/TR-06/campaign-2026-10-18/recovery-2026-10-23/root-recovery-scope.json"))
assert tr06_scope["final_Target_proved"] is False
assert not tree(TR06, "tensor-computations/TR-06/lean")
report = {
    "audit_date": "2026-10-23", "reviewer": "/root/inventory",
    "scope": "Existing full-target source/review/real-CI evidence audit, not a new mathematical review or Lean/Linux replay.",
    "published_main": MAIN, "integration_commit": INTEGRATION,
    "registry_count": len(registry), "all_registered_id_paths_preserved": True,
    "integration_status_counts": dict(Counter(integration_statuses.values())),
    "integration_remaining_solved_ids": [i for i, s in integration_statuses.items() if s == "Solved"],
    "complete_candidates": reports,
    "tr06": {"head": TR06, "status": status(TR06, registry["TR-06"]),
             "shared_support_lean_modules": len([p for p in tr06_support if p.endswith(".lean")]),
             "canonical_project_absent": True, "final_target_proved": False,
             "recovery_scope": tr06_scope,
             "readme_sha256": sha(read(TR06, "docs/lean/proofs/TR-06/README.md")),
             "remaining": "Controlled projection fiber count, graph-volume conclusion and complete Target assembly; canonical boundary/Solution and authoritative Linux receipt remain."},
    "passed": True,
}
(OUT / "audit.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"integration_commit": INTEGRATION, "status_counts": report["integration_status_counts"],
                  "complete_candidates": [r["id"] for r in reports], "tr06_complete": False,
                  "matched_real_ci_package_inputs": sum(c["inputs"] for c in CASES.values())}, indent=2))
