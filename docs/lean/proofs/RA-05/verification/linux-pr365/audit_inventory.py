#!/usr/bin/env python3
"""Independent offline audit of the actual RA05 support Linux artifact.

Reads an original artifact and raw job log, live API responses and Git objects.
Does not execute Lean, Comparator or CI and never writes canonical sources.
"""
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import zipfile

OUT = Path(__file__).resolve().parent
ROOT = next(p for p in OUT.parents if (p / ".git").exists())
ARTIFACT = Path("/private/tmp/nla-ra05-pr365-ci")
CURRENT = Path("/Users/ajt253/.codex/worktrees/solved-lean-oct23/OpenProblemsInNLA")
PROJECT = "randomized-and-low-rank-approximation/RA-05/lean"
HEAD = "0b0edfb8a75de34caec6c0f61cbf3193bbb15589"
MERGE = "4c0220b702442c97e52ae98253169e6c759010bf"
BASE = "5487945e5a72abd952b0c89915915de8cc9b3e65"
RUN = 39963923849
JOB = 120449407972
ARTIFACT_ID = 12505618149
ZIP_SHA = "09266c552e4341bf554c2d9c553331dec0dea11c43d96a3acbd6049923acfc97"
RAW_JOB_SHA = "071337faa483c1b90a514996609eb45ab095e6c676d006ad74711764eff5c2a0"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NAMES = [
    "NLA.Proofs.RA05.SupportMinimum." + n for n in [
        "rowCost_nonneg", "cost_nonneg", "strongCoreset_one", "supportSize_one",
        "minimumSupport_le_support", "minimumSupport_attained",
        "minimumSupport_le_rowCount", "minimumSupport_le_worstSupport",
    ]
] + ["NLA.Proofs.RA05." + n for n in [
    "unitHyperplane_projector", "rowCost_unitHyperplane",
    "strongCoreset_implies_allVectorEmbedding",
]]
checks = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(*args, cwd=ROOT):
    return subprocess.check_output(["git", *args], cwd=cwd)


def read(ref, path):
    return git("show", f"{ref}:{path}")


def check(name, condition, **details):
    checks.append({"name": name, "passed": bool(condition), **details})
    if not condition:
        raise AssertionError(name)


live = json.loads((OUT / "INVENTORY_LIVE_GITHUB.json").read_text())
live_jobs = live["jobs"]["value"]["structuredContent"]["jobs"]
live_artifact = live["artifacts"]["value"]["structuredContent"]["artifacts"][0]
live_pr = live["pr"]["value"]["structuredContent"]
run = json.loads((ARTIFACT / "run.json").read_text())
raw_jobs = json.loads((ARTIFACT / "jobs.json").read_text())["jobs"]
raw_artifact = json.loads((ARTIFACT / "artifact-metadata.json").read_text())
check("live-successful-exact-verification-job", any(j["id"] == JOB and j["run_id"] == RUN and j["status"] == "completed" and j["conclusion"] == "success" for j in live_jobs))
check("whole-workflow-terminal-success", run["id"] == RUN and run["event"] == "pull_request" and run["status"] == "completed" and run["conclusion"] == "success" and run["head_sha"] == HEAD)
check("retained-raw-job-metadata-agrees", any(j["id"] == JOB and j["conclusion"] == "success" and j["head_sha"] == HEAD for j in raw_jobs))
check("live-pr-head-and-synthetic-merge-identity", live_pr["number"] == 365 and live_pr["head_sha"] == HEAD and live_pr["merge_commit_sha"] == MERGE and live_pr["base_sha"] == BASE)
check("fetched-merge-parents", set(git("show", "-s", "--format=%P", MERGE).decode().split()) == {BASE, HEAD})
check("live-original-artifact-identity", live_artifact["id"] == ARTIFACT_ID and live_artifact["name"] == "lean-RA-05" and not live_artifact["expired"] and live_artifact["workflow_run"]["id"] == RUN and live_artifact["workflow_run"]["head_sha"] == HEAD)
check("retained-artifact-metadata-agrees-with-live", all(raw_artifact[k] == live_artifact[k] for k in ["id", "name", "size_in_bytes", "digest", "workflow_run"]))
zip_data = (ARTIFACT / "original-artifact.zip").read_bytes()
check("zip-equals-live-digest-and-size", sha(zip_data) == ZIP_SHA and live_artifact["digest"] == "sha256:" + ZIP_SHA and len(zip_data) == live_artifact["size_in_bytes"])
gzip_data = (ARTIFACT / f"job-{JOB}.log.gz").read_bytes()
raw_job_data = gzip.decompress(gzip_data)
raw_job = raw_job_data.decode("utf-8")
check("exact-raw-job-utf8-hash", sha(raw_job_data) == RAW_JOB_SHA)
check("actual-executed-merge-checkout", f"+{MERGE}:refs/remotes/pull/365/merge" in raw_job and f"HEAD is now at {MERGE[:8]} Merge {HEAD} into {BASE}" in raw_job)
check("raw-job-upload-binds-original-artifact", f"SHA256 digest of uploaded artifact zip is {ZIP_SHA}" in raw_job and f"Artifact ID {ARTIFACT_ID}" in raw_job and f"/actions/runs/{RUN}/artifacts/{ARTIFACT_ID}" in raw_job)
members = {}
with zipfile.ZipFile(io.BytesIO(zip_data)) as archive:
    for item in archive.infolist():
        if not item.is_dir():
            check("archive-member-safe-unique:" + item.filename, not item.filename.startswith("/") and ".." not in Path(item.filename).parts and item.filename not in members)
            members[item.filename] = archive.read(item)
extracted = {p.relative_to(ARTIFACT / "artifact").as_posix(): p.read_bytes() for p in (ARTIFACT / "artifact").rglob("*") if p.is_file()}
check("exact-original-archive-extraction-and-file-set", members == extracted)
result_members = [p for p in members if p.endswith("/result.json")]
check("exact-one-harness-result", len(result_members) == 1)
result_path = result_members[0]
verify_prefix = result_path.removesuffix("result.json")
result = json.loads(members[result_path])
check("actual-result-execution-commit-and-project", result["repository_commit"] == MERGE and result["project"] == PROJECT)
check("actual-comparator-and-leancert-kernel-acceptance", result["result"] == "comparator-accepted" and result["lean_cert_proof_trust"] == "kernel-checked" and result["verifier_profile"] == "default")
config = result["config"]
check("exact-eleven-advertised-exports-no-definition-holes", config["theorem_names"] == NAMES and config["definition_names"] == [] and config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution" and set(config["permitted_axioms"]) == STANDARD)
expected = result["input_sha256"]
check("all-forty-inputs-and-exact-source-file-set", len(expected) == 40 and set(expected) == {p.removeprefix(PROJECT + "/") for p in git("ls-tree", "-r", "--name-only", MERGE, PROJECT).decode().splitlines()})
current_status = git("status", "--porcelain", "--", PROJECT, cwd=CURRENT).decode()
check("current-canonical-package-tracked-clean", current_status == "")
inputs = []
for relative, expected_sha in expected.items():
    merge_data = read(MERGE, f"{PROJECT}/{relative}")
    head_data = read(HEAD, f"{PROJECT}/{relative}")
    current_data = (CURRENT / PROJECT / relative).read_bytes()
    check("exact-input:" + relative, sha(merge_data) == expected_sha and merge_data == head_data == current_data)
    inputs.append({"path": relative, "sha256": expected_sha, "merge_head_current_equal": True})
check("head-and-merge-exact-package-file-set", git("ls-tree", "-r", "--name-only", HEAD, PROJECT) == git("ls-tree", "-r", "--name-only", MERGE, PROJECT))
metadata = json.loads(read(MERGE, f"{PROJECT}/formalization.yaml"))
check("metadata-advertises-only-eleven-support-theorems", [r["declaration"] for r in metadata["status"]["main_results"]] == NAMES and metadata["status"]["whole_problem_verified"] is False and metadata["status"]["canonical_status"] == "Solved")
check("canonical-page-registry-and-originals-preserved", read(MERGE, "problem_ids.json") == read(BASE, "problem_ids.json") and read(MERGE, "randomized-and-low-rank-approximation/RA-05/README.md") == read(BASE, "randomized-and-low-rank-approximation/RA-05/README.md") and read(MERGE, f"{PROJECT}/sources/ORIGINAL.md") == read(BASE, "randomized-and-low-rank-approximation/RA-05/README.md") and read(MERGE, f"{PROJECT}/Reviewed/RA05.lean") == read(BASE, "lean-statements/Reviewed/RA05.lean"))
check("published-live-definitions-and-specification-preserved", all(read(MERGE, f"{PROJECT}/{p}") == read(BASE, f"lean-statements/{p}") for p in ["NLA/Statements/Infrastructure.lean", "NLA/Statements/RA05.lean", "NLA/Statements/RA06.lean"]) and read(MERGE, f"{PROJECT}/sources/NUMERICAL_TARGETS.md") == read(BASE, "docs/lean/statements/RA-05/NUMERICAL_TARGETS.md"))
approved_proofs = {
    "NLA/Proofs/RA05/SupportMinimum.lean": "d21474d121f82481cf7de107ecaa8405d0b2d12cf60c08ef75fcbea471c1f0ce",
    "NLA/Proofs/RA05/HyperplaneDefinitions.lean": "03c589f029a146203487f4d5ed5982eb67e4a91d64c0ab8f817baf1de898a276",
    "NLA/Proofs/RA05/HyperplaneBridge.lean": "2e8d441f6aa46d7344c37762010be9e1afb30574e085bad980bb9bf01e7ccae1",
}
check("independently-reviewed-proof-sources-retained", all(expected[p] == value for p, value in approved_proofs.items()))
check("published-harness-and-workflows-unchanged", git("diff", "--name-only", BASE, MERGE, "--", "tools/lean", ".github/workflows") == b"")
source_lock = read(MERGE, "tools/lean/source-lock.json")
check("pinned-checker-source-lock-and-tool-receipt", result["source_lock_sha256"] == sha(source_lock) == result["tool_receipt"]["source_lock_sha256"] and result["tool_receipt"]["forsythe_commit"] == "8d1b0c0545a77b40245e84705aa7d273e6c81e62")
check("actual-pinned-linux-runtime", "version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in result["tool_receipt"]["lean_version"] and result["tool_receipt"]["lean_toolchain"] == "leanprover/lean4:v4.33.1" and result["tool_receipt"]["platform"].startswith("Linux-"))

# Independently reproduce the exact deterministic consumer reviewed in the
# unchanged published harness; it checks theorem kind, not proposition trust.
lines = ["import Solution", "import LeanCert.Tactic.Verification", "set_option autoImplicit false", 'set_option leancert.trust "kernel"', "", "open Lean Elab Command in", 'elab "#assert_proof_constant " n:ident : command => do', "  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n", "  match (← getEnv).find? decl with", "  | some (.thmInfo _) => pure ()", '  | _ => throwErrorAt n "expected a proved theorem constant"', ""]
for name in NAMES:
    lines += [f"#assert_proof_constant {name}", f"#assert_trust kernel {name}", f"#print axioms {name}"]
consumer = "\n".join(lines) + "\n"
check("actual-generated-theorem-kind-kernel-consumer", sha(consumer.encode()) == result["lean_cert_proof_trust_source_sha256"])
trust_log = members[verify_prefix + "leancert-proof-trust.log"].decode()
check("generated-consumer-executed-successfully-under-af-unix-restriction", "ProofTrustAudit.lean" in trust_log and "RestrictAddressFamilies=~AF_UNIX" in trust_log and trust_log.rstrip().endswith("EXIT_STATUS=0"))
axiom_reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", trust_log)
check("all-eleven-actual-transitive-axiom-reports-standard-only", len(axiom_reports) == 11 and [name for name, _ in axiom_reports] == NAMES and all({a.strip() for a in axioms.split(",")} == STANDARD for _, axioms in axiom_reports))
comparator = members[verify_prefix + "comparator.log"].decode()
exports = [line for line in comparator.splitlines() if line.startswith("Exporting #[")]
check("actual-comparator-exported-eleven-from-both-modules", len(exports) == 2 and exports[0].endswith("from Challenge") and exports[1].endswith("from Solution") and all(all(name in line for name in NAMES) for line in exports))
check("actual-default-kernel-and-comparator-accepted-support-proof", "Running Lean default kernel on solution." in comparator and "Lean default kernel accepts the solution" in comparator and "Your solution is okay!" in comparator and comparator.rstrip().endswith("EXIT_STATUS=0"))
kernel = members[verify_prefix + "kernel-controls.log"].decode()
check("three-actual-builtin-kernel-controls", "RETURN honest_with_inductives_and_quotients: accepted" in kernel and "RETURN invalid_raw_proof: rejected:" in kernel and "RETURN quotient_postcheck_mismatch: rejected:" in kernel and "PASS: all three actual Comparator.runBuiltinKernel cases behaved as required" in kernel and kernel.rstrip().endswith("EXIT_STATUS=0"))
regressions = members[verify_prefix + "comparator-controls.log"].decode()
check("five-comparator-regression-controls", all(f"PASS {name}: exit" in regressions for name in ["simple_match", "simple_mismatch", "simple_axiom_issue", "simple_kind_mismatch", "type_mismatch"]) and "PASS: all five Comparator regressions" in regressions and regressions.rstrip().endswith("EXIT_STATUS=0"))
sandbox = members[verify_prefix + "sandbox.log"].decode()
check("build-and-export-real-sandbox-modes", "MODE build: exit=0" in sandbox and "MODE export: exit=0" in sandbox and sandbox.rstrip().endswith("EXIT_STATUS=0"))
for marker in ["outside .lake write-open: denied", "outside .lake truncate: denied", "symlink from .lake to outside write: denied", "outside .lake creation: denied", "user namespace: private", "pid namespace: private", "mnt namespace: private", "net namespace: private", "ipc namespace: private", "uts namespace: private", "host parent: absent from private /proc", "host parent signal lookup: denied", "host loopback listener: unreachable", "AF_UNIX socket creation: denied", "effective capabilities: none", "no_new_privs: set", "nested namespace write attempt: rejected"]:
    check("both-sandbox-modes:" + marker, sandbox.count("PASS " + marker) == 2)
check("build-only-designated-write-and-readonly-export", "PASS build .lake write: allowed" in sandbox and "PASS export .lake write-open: denied" in sandbox and "PASS export .lake truncate: denied" in sandbox)
check("four-negative-sandbox-option-controls", all(f"NEGATIVE {name}: exit=2" in sandbox for name in ["unknown option", "unexpected --rw", "unexpected --rwx", "relative --rwx"]))
sorry = members[verify_prefix + "negative-sorry.log"].decode()
native = members[verify_prefix + "negative-native.log"].decode()
check("sorry-admission-rejected", "Illegal axiom detected: 'sorryAx'" in sorry and sorry.rstrip().endswith("EXIT_STATUS=1"))
check("native-evaluation-axiom-rejected", "Illegal axiom detected:" in native and "native_decide.ax_1_1" in native and native.rstrip().endswith("EXIT_STATUS=1"))
dependencies = members[verify_prefix + "dependencies.log"].decode()
manifest = json.loads(read(MERGE, f"{PROJECT}/lake-manifest.json"))
check("all-ten-dependency-pins-materialized", len(manifest["packages"]) == 10 and all("checking out revision '" + p["rev"] + "'" in dependencies for p in manifest["packages"]) and dependencies.rstrip().endswith("EXIT_STATUS=0"))
check("leancert-real-consumer-library-build-success", "lake build LeanCert.Tactic.Verification" in members[verify_prefix + "leancert-build.log"].decode() and members[verify_prefix + "leancert-build.log"].decode().rstrip().endswith("EXIT_STATUS=0"))
check("user-service-denies-af-unix-and-succeeds", "RestrictAddressFamilies=~AF_UNIX" in members[verify_prefix + "user-service.log"].decode() and members[verify_prefix + "user-service.log"].decode().rstrip().endswith("EXIT_STATUS=0"))
check("actual-bootstrap-built-default-checker-and-exporter", "lake build lean4export comparator" in members["bootstrap/comparator-build.log"].decode() and members["bootstrap/comparator-build.log"].decode().rstrip().endswith("EXIT_STATUS=0"))
check("raw-job-reports-complete-harness-success", "PASS: fresh Comparator run and all controls." in raw_job)

retained = OUT / "retained"
retained.mkdir(exist_ok=True)
for name in ["original-artifact.zip", f"job-{JOB}.log.gz", "run.json", "jobs.json", "artifacts.json", "artifact-metadata.json"]:
    shutil.copyfile(ARTIFACT / name, retained / name)
(OUT / "reconstructed_ProofTrustAudit.lean.txt").write_text(consumer)
report = {
    "reviewer": "/root/inventory", "date": "2026-10-23",
    "scope": "Independent offline audit of actual Linux CI for eleven RA05 support exports only; not a full RA05 proof or a local Linux/Lean rerun.",
    "run": RUN, "job": JOB, "artifact": ARTIFACT_ID,
    "source_pr_head": HEAD, "actual_executed_synthetic_merge": MERGE, "base": BASE,
    "current_worktree": str(CURRENT), "current_worktree_head": git("rev-parse", "HEAD", cwd=CURRENT).decode().strip(),
    "archive_sha256": ZIP_SHA, "raw_job_utf8_sha256": RAW_JOB_SHA,
    "raw_job_gzip_sha256": sha(gzip_data), "input_count": len(expected),
    "lean_input_count_including_two_historical_challenges": sum(p.endswith(".lean") for p in expected),
    "actual_selected_exports": NAMES, "proof_trust": result["lean_cert_proof_trust"],
    "result": result["result"], "whole_problem_verified": False,
    "canonical_status": "Solved", "consumer_sha256": sha(consumer.encode()),
    "checks": checks, "all_merge_head_current_inputs": inputs,
    "artifact_member_sha256": {p: sha(b) for p, b in sorted(members.items())},
    "result_sha256": sha(members[result_path]), "tool_receipt": result["tool_receipt"],
    "retained_original_sources": {p.name: sha(p.read_bytes()) for p in retained.iterdir() if p.is_file()},
    "limits": ["Execution identity is merge 4c0220b7; head 0b0edfb8 has identical 40 project inputs, not the same execution commit.", "These eleven theorems are support only; full Classification and NegativeAnswer remain unproved.", "This independently checks retained actual Linux evidence; it does not rerun Lean or Comparator locally."],
    "passed": all(c["passed"] for c in checks),
}
(OUT / "INVENTORY_REVIEW.json").write_text(json.dumps(report, indent=2) + "\n")
print(f"PASS: {len(checks)} evidence checks; 40 exact merge/head/current inputs; 11 selected support exports")
