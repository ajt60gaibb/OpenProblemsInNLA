#!/usr/bin/env python3
"""Audit downloaded full PF05 Linux CI evidence against exact committed inputs.

This reads actual retained logs. It does not recreate Linux or rerun Comparator.
"""
import argparse
import ast
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import zipfile

REPO = Path(__file__).resolve().parents[5]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--ref", required=True, help="Exact source commit of the retained completed workflow")
parser.add_argument("--artifact", type=Path, required=True)
parser.add_argument("--metadata", type=Path, required=True)
parser.add_argument("--job-log-gz", type=Path, required=True)
parser.add_argument("--archive", type=Path, required=True)
parser.add_argument("--artifact-metadata", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--reviewer", default="/root (Codex AI agent; retained CI artifact audit)")
args = parser.parse_args()
PROJECT = "nonnegative-and-positive-factorizations/PF-05/lean"
TARGET = "NLA.PF05.target"
checks = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def source(path, ref=None):
    return subprocess.check_output(["git", "show", f"{ref or args.ref}:{path}"], cwd=REPO)


def check(name, passed, **evidence):
    checks.append({"name": name, "passed": bool(passed), **evidence})


paths = list(args.artifact.rglob("result.json"))
if len(paths) != 1:
    raise RuntimeError("Expected exactly one completed harness result.json")
logs = paths[0].parent
result = json.loads(paths[0].read_text())
metadata = json.loads(args.metadata.read_text())
job = next(j for j in metadata["jobs"] if j["name"] == "verify (PF-05, " + PROJECT + ")")
check("github-workflow-success", metadata["status"] == "completed" and metadata["conclusion"] == "success")
check("github-PF05-job-success", job["status"] == "completed" and job["conclusion"] == "success", job_id=job["databaseId"])
check("github-source-commit", metadata["headSha"] == args.ref, expected=args.ref, observed=metadata["headSha"])
check("harness-source-commit", result["repository_commit"] == args.ref, observed=result["repository_commit"])
check("canonical-project", result["project"] == PROJECT)
check("comparator-accepted", result["result"] == "comparator-accepted")
check("leancert-kernel-checked", result["lean_cert_proof_trust"] == "kernel-checked")
check("default-verifier-profile", result.get("verifier_profile", "default") == "default")
config = json.loads(source(PROJECT + "/comparator.json"))
check("exact-config-in-result", config == result["config"])
check("full-target-only-without-holes", config == {
    "challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": [TARGET],
    "definition_names": [], "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]})
check("solution-literal-frozen-target", b"theorem target : NLA.Statements.PF05.Target := by" in source(PROJECT + "/Solution.lean"))
check("solution-uses-closed-shared-proof", b"exact NLA.Proofs.PF05.target" in source(PROJECT + "/Solution.lean"))
check("unchanged-published-Target", source(PROJECT + "/NLA/Statements/PF05.lean") ==
      source("lean-statements/NLA/Statements/PF05.lean", "36767fa430309f13d04dc6ebe080d470f5c2444a"))

proof_lock = json.loads(source(PROJECT + "/proof-source-lock.json"))
expected_lean = {item["destination"][len(PROJECT)+1:] for item in proof_lock["copies"]}
expected_lean.update({"Reviewed/PF05.lean", "Challenge.lean", "Identity.lean", "Solution.lean"})
check("exact-reviewed-46-Lean-input-set", len(expected_lean) == 46
      and {name for name in result["input_sha256"] if name.endswith(".lean")} == expected_lean,
      count=len(expected_lean))

inputs = []
for name, expected in result["input_sha256"].items():
    committed = sha(source(PROJECT + "/" + name))
    working = REPO / PROJECT / name
    current = sha(working.read_bytes()) if working.is_file() else None
    inputs.append({"path": name, "expected_sha256": expected,
                   "committed_sha256": committed, "current_sha256": current,
                   "committed_matches": committed == expected, "current_matches": current == expected})
check("all-inputs-match-recorded-commit", all(i["committed_matches"] for i in inputs), count=len(inputs))
check("all-inputs-match-current-package", all(i["current_matches"] for i in inputs), count=len(inputs))
for ref, label in [(args.ref, "recorded-commit"), ("HEAD", "current-HEAD")]:
    tree = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", "-z", ref, "--", PROJECT], cwd=REPO).decode().split("\0")
    names = {name[len(PROJECT)+1:] for name in tree if name}
    check("exact-project-file-set:" + label, names == set(result["input_sha256"]),
          added=sorted(names-set(result["input_sha256"])), missing=sorted(set(result["input_sha256"])-names))
lock = sha(source("tools/lean/source-lock.json"))
check("pinned-checker-source-lock", lock == result["source_lock_sha256"] == result["tool_receipt"]["source_lock_sha256"], sha256=lock)
receipt = result["tool_receipt"]
check("real-linux-toolchain", "Linux" in receipt["platform"]
      and receipt["lean_toolchain"] == "leanprover/lean4:v4.33.1"
      and "x86_64-unknown-linux-gnu" in receipt["lean_version"]
      and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in receipt["lean_version"], receipt=receipt)
source_lock = json.loads(source("tools/lean/source-lock.json"))
check("pinned-Forsythe-checker-commit", receipt["forsythe_commit"] == source_lock["commit"])
check("recorded-checker-exporter-sandbox-binaries", set(receipt["executables"]) == {
    ".tools/comparator/.lake/build/bin/comparator", ".tools/lean4export/.lake/build/bin/lean4export", ".tools/bin/landrun"}
    and all(re.fullmatch(r"[0-9a-f]{64}", h) for h in receipt["executables"].values()))

module = ast.parse(source("tools/lean/harness.py"))
function = next(n for n in module.body if isinstance(n, ast.FunctionDef) and n.name == "proof_trust_source")
env = {"MODULE": re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z"), "HarnessError": RuntimeError}
exec(compile(ast.Module(body=[function], type_ignores=[]), "committed-proof-trust-generator", "exec"), env)
audit = env["proof_trust_source"](config)
check("reproduce-actual-generated-kernel-consumer", sha(audit.encode()) == result["lean_cert_proof_trust_source_sha256"], sha256=sha(audit.encode()))
check("consumer-theorem-kind-and-kernel", "some (.thmInfo _)" in audit
      and f"#assert_proof_constant {TARGET}" in audit and f"#assert_trust kernel {TARGET}" in audit)
trust_log = (logs / "leancert-proof-trust.log").read_text()
check("actual-export-standard-axioms", f"'{TARGET}' depends on axioms: [propext, Classical.choice, Quot.sound]" in trust_log)
markers = {
    "comparator.log": ["Running Lean default kernel on solution.", "Lean default kernel accepts the solution", "Your solution is okay!", "EXIT_STATUS=0", "scripts/strict_landrun.py", "systemd-run --user"],
    "leancert-proof-trust.log": ["EXIT_STATUS=0"],
    "leancert-build.log": ["EXIT_STATUS=0"],
    "dependencies.log": ["EXIT_STATUS=0"],
    "mathlib-cache.log": ["EXIT_STATUS=0"],
    "user-service.log": ["EXIT_STATUS=0"],
    "kernel-controls.log": ["PASS: all three actual Comparator.runBuiltinKernel cases behaved as required", "EXIT_STATUS=0"],
    "comparator-controls.log": ["PASS: all five Comparator regressions", "EXIT_STATUS=0"],
    "sandbox.log": ["MODE build: exit=0", "MODE export: exit=0", "PASS build .lake write: allowed", "PASS export .lake write-open: denied", "PASS host loopback listener: unreachable", "PASS AF_UNIX socket creation: denied", "PASS effective capabilities: none", "PASS no_new_privs: set", "NEGATIVE unknown option: exit=2", "NEGATIVE unexpected --rw: exit=2", "NEGATIVE unexpected --rwx: exit=2", "NEGATIVE relative --rwx: exit=2", "Outer and export fixture contents unchanged; only designated build fixture written.", "EXIT_STATUS=0"],
    "negative-sorry.log": ["Illegal axiom detected: 'sorryAx'", "EXIT_STATUS=1"],
    "negative-native.log": ["Illegal axiom detected: 'checked._native.native_decide.ax_1_1'", "EXIT_STATUS=1"],
}
for name, required in markers.items():
    observed = (logs / name).read_text()
    check("actual-log-markers:" + name, all(m in observed for m in required), required=required)
job_raw = gzip.decompress(args.job_log_gz.read_bytes())
job_text = job_raw.decode()
check("raw-job-log-has-harness-success", "PASS: fresh Comparator run and all controls." in job_text
      and "Artifact lean-PF-05 has been successfully uploaded!" in job_text)
archive_sha = sha(args.archive.read_bytes())
artifact_metadata = json.loads(args.artifact_metadata.read_text())
check("original-archive-matches-GitHub-digest", artifact_metadata["digest"] == "sha256:" + archive_sha,
      sha256=archive_sha)
check("original-archive-matches-job-upload", "SHA256 digest of uploaded artifact zip is " + archive_sha in job_text)
check("artifact-metadata-binds-run-and-head", artifact_metadata["workflow_run"]["id"] == metadata["databaseId"]
      and artifact_metadata["workflow_run"]["head_sha"] == args.ref and artifact_metadata["name"] == "lean-PF-05"
      and not artifact_metadata["expired"], artifact_id=artifact_metadata["id"])
with zipfile.ZipFile(args.archive) as archive:
    archived = {name: sha(archive.read(name)) for name in archive.namelist() if not name.endswith("/")}
downloaded = {str(p.relative_to(args.artifact)): sha(p.read_bytes())
              for p in args.artifact.rglob("*") if p.is_file()}
check("downloaded-extraction-equals-original-archive", archived == downloaded, file_count=len(archived))
report = {"schema_version": 1, "reviewer": args.reviewer,
          "scope": "Actual completed Linux full-Target Comparator/kernel artifact and exact committed/current source correspondence",
          "source_commit": args.ref, "run": metadata["url"], "job": job["url"],
          "github_metadata_sha256": sha(args.metadata.read_bytes()),
          "job_log_uncompressed_sha256": sha(job_raw), "job_log_gzip_sha256": sha(args.job_log_gz.read_bytes()),
          "archive_sha256": archive_sha, "artifact_metadata_sha256": sha(args.artifact_metadata.read_bytes()),
          "artifact_id": artifact_metadata["id"],
          "checks": checks, "inputs": inputs,
          "artifact_file_sha256": {str(p.relative_to(args.artifact)): sha(p.read_bytes())
                                    for p in sorted(args.artifact.rglob("*")) if p.is_file()},
          "passed": all(c["passed"] for c in checks),
          "limitations": ["This audit independently read downloaded actual CI artifacts; it did not rerun Linux Comparator or rebuild its tools locally.",
                          "Semantic fidelity is supplied by the separate hash-bound exact statement and complete proof reviews.",
                          "Checker, toolchain and dependency-cache trust remain the pinned harness trust model recorded in its receipt."]}
args.output.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"passed": report["passed"], "checks": len(checks), "inputs": len(inputs),
                  "failed_checks": [c["name"] for c in checks if not c["passed"]]}, indent=2))
raise SystemExit(0 if report["passed"] else 1)
