#!/usr/bin/env python3
"""Check historical FR-05 CI evidence against its receipt and current bytes.

This script does not execute Lean, Comparator, or a Linux sandbox.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[4])
parser.add_argument("--ref", default="47006df8b3a6c724a557266c891893d03e69323a")
parser.add_argument("--artifact", type=Path, default=Path(__file__).with_name("fr05-linux-artifact"))
parser.add_argument("--metadata", type=Path, default=Path(__file__).with_name("fr05-run-metadata.json"))
parser.add_argument("--output", type=Path, default=Path(__file__).with_name("fr05-artifact-check.json"))
args = parser.parse_args()
PROJECT = "frames-and-matrix-designs/FR-05/lean"
RUN = "https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/38000947893"
checks = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def source(path):
    return subprocess.check_output(["git", "show", f"{args.ref}:{path}"], cwd=args.repo)


def check(name, passed, **evidence):
    checks.append({"name": name, "passed": bool(passed), **evidence})


result_paths = list(args.artifact.rglob("result.json"))
if len(result_paths) != 1:
    raise RuntimeError("Expected exactly one historical result.json")
logs = result_paths[0].parent
result = json.loads(result_paths[0].read_text())
receipt = source("docs/lean/proofs/FR-05/LINUX_CI_RECEIPT.md").decode()
receipt_hashes = dict(re.findall(r"\| `([^`]+)` \| `([a-f0-9]{64})` \|", receipt))
check("receipt_has_four_key_artifact_hashes", len(receipt_hashes) == 4)
for name, expected in receipt_hashes.items():
    observed = sha((logs / name).read_bytes())
    check("artifact_receipt_hash:" + name, observed == expected, expected=expected, observed=observed)
check("historical_commit", result["repository_commit"] == "e70f6976c51d4ef1246b395aeb0ff0678b9483e1")
check("historical_project", result["project"] == PROJECT)
check("comparator_accepted", result["result"] == "comparator-accepted")
check("leancert_kernel_checked", result["lean_cert_proof_trust"] == "kernel-checked")
config = json.loads(source(PROJECT + "/comparator.json"))
check("current_comparator_selection_exact", config == result["config"], selection=config)
check("no_definition_holes", config["definition_names"] == [])
check("foundational_axiom_allowlist", set(config["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"})

input_records = []
for name, expected in result["input_sha256"].items():
    published = source(PROJECT + "/" + name)
    working = args.repo / PROJECT / name
    observed = sha(published)
    current = sha(working.read_bytes()) if working.is_file() else None
    input_records.append({"path": name, "expected": expected,
                          "published_sha256": observed, "current_worktree_sha256": current,
                          "published_matches": observed == expected, "worktree_matches": current == expected})
check("all_historical_inputs_match_published", all(item["published_matches"] for item in input_records), count=len(input_records))
check("all_historical_inputs_match_current_worktree", all(item["worktree_matches"] for item in input_records), count=len(input_records))
tree = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", "-z", args.ref, "--", PROJECT], cwd=args.repo).decode().split("\0")
current_paths = {name[len(PROJECT) + 1:] for name in tree if name}
check("published_project_file_set_exact", current_paths == set(result["input_sha256"]),
      added=sorted(current_paths - set(result["input_sha256"])),
      missing=sorted(set(result["input_sha256"]) - current_paths))
lock = sha(source("tools/lean/source-lock.json"))
check("checker_source_lock_unchanged", lock == result["source_lock_sha256"] == result["tool_receipt"]["source_lock_sha256"], sha256=lock)
check("linux_lean_4331", result["tool_receipt"]["lean_toolchain"] == "leanprover/lean4:v4.33.1"
      and "Linux" in result["tool_receipt"]["platform"], receipt=result["tool_receipt"])

module = ast.parse(source("tools/lean/harness.py"))
function = next(node for node in module.body if isinstance(node, ast.FunctionDef) and node.name == "proof_trust_source")
env = {"MODULE": re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z"), "HarnessError": RuntimeError}
exec(compile(ast.Module(body=[function], type_ignores=[]), "published-proof-trust-generator", "exec"), env)
audit = env["proof_trust_source"](config)
check("current_audit_generator_reproduces_historical_source", sha(audit.encode()) == result["lean_cert_proof_trust_source_sha256"], sha256=sha(audit.encode()))
check("audit_requires_theorem_constants", "some (.thmInfo _)" in audit)
trust_log = (logs / "leancert-proof-trust.log").read_text()
for name in config["theorem_names"]:
    expected_line = f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
    check("historical_export_axioms:" + name, expected_line in trust_log)

markers = {
    "comparator.log": ["Lean default kernel accepts the solution", "Your solution is okay!", "EXIT_STATUS=0"],
    "leancert-proof-trust.log": ["EXIT_STATUS=0"],
    "leancert-build.log": ["EXIT_STATUS=0"],
    "kernel-controls.log": ["PASS: all three actual Comparator.runBuiltinKernel cases behaved as required", "EXIT_STATUS=0"],
    "comparator-controls.log": ["PASS: all five Comparator regressions", "EXIT_STATUS=0"],
    "sandbox.log": ["Outer and export fixture contents unchanged; only designated build fixture written.", "EXIT_STATUS=0"],
    "negative-sorry.log": ["Illegal axiom detected: 'sorryAx'", "EXIT_STATUS=1"],
    "negative-native.log": ["Illegal axiom detected: 'checked._native.native_decide.ax_1_1'", "EXIT_STATUS=1"],
}
for name, required in markers.items():
    text = (logs / name).read_text()
    check("historical_log_markers:" + name, all(marker in text for marker in required), required=required)

metadata = json.loads(args.metadata.read_text())
job = next(job for job in metadata["jobs"] if job["databaseId"] == 114058782811)
check("github_fr05_job_succeeded", job["status"] == "completed" and job["conclusion"] == "success", job=job)
check("github_head_matches_receipt", metadata["headSha"] == "1d262c8609a6ba3cfd85989fa8ac1317a04fec93")
report = {
    "schema_version": 1, "reviewer": "/root/lean_verification (independent Codex AI agent)",
    "checked_on": "2026-10-17", "scope": "Historical Linux artifact integrity and exact current source correspondence",
    "published_ref": args.ref, "run": RUN, "run_conclusion": metadata["conclusion"],
    "fr05_job_conclusion": job["conclusion"], "artifact_root": str(args.artifact),
    "historical_repository_commit": result["repository_commit"],
    "checks": checks, "inputs": input_records,
    "artifact_file_sha256": {str(path.relative_to(args.artifact)): sha(path.read_bytes()) for path in sorted(args.artifact.rglob("*")) if path.is_file()},
    "passed": all(item["passed"] for item in checks),
    "limitations": [
        "This audit did not execute Lean, Comparator, exporter, or the Linux sandbox anew.",
        "The successful historical FR-05 job is distinguished from its overall multi-project workflow, whose conclusion was cancelled.",
        "The historical result and source hashes are evidence of the recorded Linux check; semantic fidelity relies separately on the retained independent mathematical review.",
        "Compiled dependency cache and checker/toolchain trust are the historical harness trust model; this audit did not rebuild those tools.",
    ],
}
args.output.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"passed": report["passed"], "checks": len(checks), "inputs": len(input_records),
                  "failed_checks": [item["name"] for item in checks if not item["passed"]], "output": str(args.output)}, indent=2))
raise SystemExit(0 if report["passed"] else 1)
