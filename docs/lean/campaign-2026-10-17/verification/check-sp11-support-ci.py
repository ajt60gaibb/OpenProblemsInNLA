#!/usr/bin/env python3
"""Independently audit the retained seven-module Linux support CI receipt."""
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess

REPO = Path(__file__).resolve().parents[4]
EVIDENCE = Path(__file__).with_name("sp11-linux-ci")
receipt = json.loads((EVIDENCE / "receipt.json").read_text())
metadata = json.loads((EVIDENCE / "run.json").read_text())
result_path, = (EVIDENCE / "comparator-identities").rglob("result.json")
result = json.loads(result_path.read_text())
log_raw = gzip.decompress((EVIDENCE / "statement-boundaries.log.gz").read_bytes())
log = log_raw.decode()
checks = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check(name, passed, **details):
    checks.append({"name": name, "passed": bool(passed), **details})


check("run_succeeded", metadata["conclusion"] == "success")
check("proof_revision", metadata["headSha"] == receipt["proof_revision"] == "e65f2892c7431202c49bf81cc09d8f5f88256343")
check("merge_revision", result["repository_commit"] == receipt["repository_merge_revision"] == "95cfb5117171780bb16b93f6d7be7fe568c09e0d")
for job_id in [117460669321, 117464679966]:
    job, = [job for job in metadata["jobs"] if job["databaseId"] == job_id]
    check("job_succeeded:" + str(job_id), job["status"] == "completed" and job["conclusion"] == "success", name_in_ci=job["name"], url=job["url"])
check("statement_job_log_digest", sha(log_raw) == receipt["statement_job_log_uncompressed_sha256"] == "181e1690e0b2b77a09ac7feff551c8bf6f6b389d7c47c434b28958bb57ad8820")
check("aggregate_build_completed", "Build completed successfully (9006 jobs)." in log)
for path, expected in receipt["support_source_sha256"].items():
    current = sha((REPO / path).read_bytes())
    historical = sha(subprocess.check_output(["git", "show", f"{receipt['proof_revision']}:{path}"], cwd=REPO))
    name = Path(path).stem
    check("support_source_identity:" + name, current == historical == expected, sha256=current)
    check("actual_module_built:" + name, bool(re.search(r"Built NLA\.Proofs\.SP11\." + name + r"\s+\(", log)))

inputs = []
for path, expected in result["input_sha256"].items():
    file = REPO / result["project"] / path
    actual = sha(file.read_bytes()) if file.is_file() else None
    inputs.append({"path": path, "expected": expected, "observed": actual, "passed": actual == expected})
check("all_458_recorded_snapshot_inputs_match_current", len(inputs) == 458 and all(item["passed"] for item in inputs), input_count=len(inputs))
names = result["config"]["theorem_names"]
identity_names = [name for name in names if name.startswith("NLA.Statements.ComparatorControl.identity_")]
control_names = [name for name in names if name not in identity_names]
check("selected_scope_is_45_identities_and_one_control", len(identity_names) == 45 and control_names == ["NLA.Statements.ComparatorControl.log_two_upper"], identities=identity_names, controls=control_names)
check("sp11_selection_is_statement_identity", "NLA.Statements.ComparatorControl.identity_SP11" in names and not any(name.startswith("NLA.Proofs.SP11.") for name in names))
check("no_definition_holes", result["config"]["definition_names"] == [])
check("foundational_allowlist", set(result["config"]["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"})
check("comparator_accepted", result["result"] == receipt["comparator_result"] == "comparator-accepted")
check("leancert_kernel_checked", result["lean_cert_proof_trust"] == "kernel-checked")
required = {
    "comparator.log": ["Lean default kernel accepts the solution", "Your solution is okay!", "EXIT_STATUS=0"],
    "leancert-proof-trust.log": ["EXIT_STATUS=0"],
    "leancert-build.log": ["EXIT_STATUS=0"],
    "kernel-controls.log": ["PASS: all three actual Comparator.runBuiltinKernel cases behaved as required", "EXIT_STATUS=0"],
    "comparator-controls.log": ["PASS: all five Comparator regressions", "EXIT_STATUS=0"],
    "sandbox.log": ["Outer and export fixture contents unchanged; only designated build fixture written.", "EXIT_STATUS=0"],
    "negative-sorry.log": ["Illegal axiom detected: 'sorryAx'", "EXIT_STATUS=1"],
    "negative-native.log": ["Illegal axiom detected: 'checked._native.native_decide.ax_1_1'", "EXIT_STATUS=1"],
}
for name, markers in required.items():
    text = (result_path.parent / name).read_text()
    check("control_and_result_log:" + name, all(marker in text for marker in markers))
check("receipt_does_not_claim_full_target", receipt["full_sp11_target_proved"] is False)
report = {"schema_version": 1, "checked_on": "2026-10-17", "reviewer": "/root/lean_verification (independent AI agent)",
          "scope": "Independent retained-artifact/source correspondence audit; seven support modules only",
          "checks": checks, "snapshot_inputs": inputs,
          "evidence_sha256": {str(path.relative_to(EVIDENCE)): sha(path.read_bytes()) for path in sorted(EVIDENCE.rglob("*")) if path.is_file()},
          "passed": all(item["passed"] for item in checks),
          "limitations": ["No new Linux/Lean/Comparator execution or fresh GitHub log retrieval was performed by this audit.",
                          "The isolated Comparator selects frozen statement identities and an infrastructure certificate, not the SP-11 proof support theorems or a complete SP-11 solution.",
                          "New modules added after proof revision e65f2892 are outside this seven-module Linux receipt."]}
output = Path(__file__).with_name("sp11-support-ci-independent-audit.json")
output.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"passed": report["passed"], "checks": len(checks), "inputs": len(inputs),
                  "failed": [item["name"] for item in checks if not item["passed"]], "output": str(output)}, indent=2))
raise SystemExit(0 if report["passed"] else 1)
