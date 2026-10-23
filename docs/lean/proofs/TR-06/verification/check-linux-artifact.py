#!/usr/bin/env python3
"""Audit downloaded full TR06 Linux CI evidence against exact committed inputs.

This reads actual retained logs. It does not recreate Linux or rerun Comparator.
"""
import argparse
import ast
import gzip
from functools import lru_cache
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
PROJECT = "tensor-computations/TR-06/lean"
TARGET = "NLA.TR06.target"
PUBLISHED = "3da7a876b97815c99ebde0f4f9c17932096345a2"
ORIGINAL_STATEMENT = "36767fa430309f13d04dc6ebe080d470f5c2444a"
BEFORE_SOLUTION_LOCK = "docs/lean/proofs/TR-06/canonical-boundary-before-solution/source-lock.json"
BEFORE_SOLUTION_LOCK_SHA256 = "ac6bb715222b2190b7feb7a21e0c49c5a3825ccb459fb43a98a37342258605db"
RETAINED_LOCK = "docs/lean/proofs/TR-06/campaign-2026-10-18/retained-58-source-lock.json"
PUBLISHED_EXPORTS = [
    "NLA.TR06.derivativeRatio_eq_operatorNorm",
    "NLA.TR06.angularSlope_eq_chart_derivative",
    "NLA.TR06.induced_volume_chart",
    "NLA.TR06.regular_locus",
    "NLA.TR06.finite_angular_mean",
    "NLA.TR06.generic_iff_source",
    "NLA.TR06.smooth_locus_correspondence",
    "NLA.TR06.smooth_chart_is_local_addition_inverse",
    "NLA.TR06.source_model_correspondence",
    "NLA.TR06.finite_angular_mean_source",
]
TARGETS = PUBLISHED_EXPORTS + [TARGET]
STANDARD_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
EXPECTED_COUNTS = {"selected_exports": 11, "canonical_Lean_inputs": 144,
                   "copied_sources": 140, "proof_sources": 80, "retained_sources": 58}
BASE_CONTROL_COUNT = 41
ADDITIONAL_CONTROL_COUNT = 4
checks = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


@lru_cache(maxsize=None)
def source(path, ref=None):
    return subprocess.check_output(["git", "show", f"{ref or args.ref}:{path}"], cwd=REPO)


def check(name, passed, **evidence):
    checks.append({"name": name, "passed": bool(passed), **evidence})


def parse_axiom_records(text):
    records = {}
    for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        axioms = [item.strip() for item in body.split(",") if item.strip()]
        records.setdefault(name, []).append(axioms)
    return records


def current_sha(path):
    file = REPO / path
    return sha(file.read_bytes()) if file.is_file() else None


paths = list(args.artifact.rglob("result.json"))
if len(paths) != 1:
    raise RuntimeError("Expected exactly one completed harness result.json")
logs = paths[0].parent
result = json.loads(paths[0].read_text())
metadata = json.loads(args.metadata.read_text())
job = next(j for j in metadata["jobs"] if j["name"] == "verify (TR-06, " + PROJECT + ")")
check("github-workflow-success", metadata["status"] == "completed" and metadata["conclusion"] == "success")
check("github-TR06-job-success", job["status"] == "completed" and job["conclusion"] == "success", job_id=job["databaseId"])
check("github-source-commit", metadata["headSha"] == args.ref, expected=args.ref, observed=metadata["headSha"])
check("harness-source-commit", result["repository_commit"] == args.ref, observed=result["repository_commit"])
check("canonical-project", result["project"] == PROJECT)
check("comparator-accepted", result["result"] == "comparator-accepted")
check("leancert-kernel-checked", result["lean_cert_proof_trust"] == "kernel-checked")
check("default-verifier-profile", result.get("verifier_profile", "default") == "default")
config = json.loads(source(PROJECT + "/comparator.json"))
check("exact-config-in-result", config == result["config"])
check("full-target-and-ten-published-exports-without-holes", config == {
    "challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": TARGETS,
    "definition_names": [], "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]})
check("solution-literal-frozen-target", b"theorem target : NLA.Statements.TR06.Target := by" in source(PROJECT + "/Solution.lean"))
check("solution-uses-closed-shared-proof", b"exact NLA.Proofs.TR06.target" in source(PROJECT + "/Solution.lean"))
check("unchanged-published-Target", source(PROJECT + "/NLA/Statements/TR06.lean") ==
      source("lean-statements/NLA/Statements/TR06.lean", ORIGINAL_STATEMENT))

proof_lock = json.loads(source(PROJECT + "/proof-source-lock.json"))
expected_lean = {item["destination"][len(PROJECT)+1:] for item in proof_lock["copies"]}
expected_lean.update({"Reviewed/TR06.lean", "Challenge.lean", "Identity.lean", "Solution.lean"})
check("exact-reviewed-144-Lean-input-set", len(expected_lean) == 144
      and {name for name in result["input_sha256"] if name.endswith(".lean")} == expected_lean,
      count=len(expected_lean))

# Additional guards bind every copy to its exact shared source and the
# immutable original candidate. These supplement, rather than replace, the
# inherited actual-commit/current-package and complete input-set controls.
copy_records = []
for item in proof_lock["copies"]:
    src = item["source"]
    dest = item["destination"]
    expected_path = item["module"].replace(".", "/") + ".lean"
    source_sha = sha(source(src))
    destination_sha = sha(source(dest))
    copy_records.append({"source": src, "destination": dest,
                         "module": item["module"],
                         "source_sha256": source_sha,
                         "destination_sha256": destination_sha,
                         "current_source_sha256": current_sha(src),
                         "current_destination_sha256": current_sha(dest),
                         "passed": src == "lean-statements/" + expected_path
                         and dest == PROJECT + "/" + expected_path
                         and item["source_sha256"] == item["destination_sha256"]
                         == source_sha == destination_sha == current_sha(src) == current_sha(dest)})
proof_count = sum(item["module"].startswith("NLA.Proofs.TR06.") for item in proof_lock["copies"])
retained_count = sum(item["module"].startswith("NLA.TR06.") for item in proof_lock["copies"])
statement_count = sum(item["module"].startswith("NLA.Statements.") for item in proof_lock["copies"])
package_exports = proof_lock["package_exports"]
expected_package_exports = {"Challenge.lean", "Identity.lean", "Solution.lean", "Reviewed/TR06.lean",
                            "comparator.json", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
                            "ORIGINAL.md", "LICENSE"}
check("proof-lock-exact-140-copies-80-proof-58-retained", len(copy_records) == 140
      and len({item["source"] for item in copy_records}) == 140
      and len({item["destination"] for item in copy_records}) == 140
      and proof_count == 80 and retained_count == 58 and statement_count == 2
      and proof_lock["retained_source_count"] == 58
      and proof_lock["actual_copied_source_count"] == 140
      and proof_lock["actual_proof_source_count"] == 80
      and proof_lock["actual_canonical_Lean_input_count"] == 144
      and proof_lock["entry"] == "NLA.Proofs.TR06.RetainedBoundaryMean"
      and proof_lock["selected_exports"] == TARGETS
      and all(item["passed"] for item in copy_records)
      and set(package_exports) == expected_package_exports
      and all(sha(source(PROJECT + "/" + name)) == expected == current_sha(PROJECT + "/" + name)
              for name, expected in package_exports.items()),
      copied=len(copy_records), proof=proof_count, retained=retained_count, statements=statement_count)

retained_lock = json.loads(source(RETAINED_LOCK))
published_tree = subprocess.check_output(
    ["git", "ls-tree", "-r", "--name-only", "-z", PUBLISHED, "--", PROJECT + "/NLA/TR06"],
    cwd=REPO).decode().split("\0")
published_paths = {path for path in published_tree if path.endswith(".lean")}
retained_records = []
for item in retained_lock["records"]:
    published_sha = sha(source(item["published_path"], PUBLISHED))
    canonical_sha = sha(source(item["published_path"]))
    shared_sha = sha(source(item["campaign_path"]))
    retained_records.append({**item, "published_sha256": published_sha,
                             "canonical_sha256": canonical_sha, "shared_sha256": shared_sha,
                             "passed": published_sha == item["sha256"] == canonical_sha == shared_sha
                             == current_sha(item["published_path"]) == current_sha(item["campaign_path"])})
check("unchanged-58-published-retained-sources", retained_lock["published_commit"] == PUBLISHED
      and retained_lock["copy_count"] == 58 and len(retained_records) == 58
      and len(published_paths) == 58
      and {item["published_path"] for item in retained_records} == published_paths
      and {item["published_path"] for item in retained_records} ==
          {item["destination"] for item in proof_lock["copies"] if item["module"].startswith("NLA.TR06.")}
      and all(item["passed"] for item in retained_records), count=len(retained_records), base=PUBLISHED)

published_config = json.loads(source(PROJECT + "/comparator.json", PUBLISHED))
published_challenge = source(PROJECT + "/Challenge.lean", PUBLISHED)
challenge = source(PROJECT + "/Challenge.lean")
intrinsic_import = b"import NLA.Statements.TR06\n"
before_lock_bytes = source(BEFORE_SOLUTION_LOCK)
before_lock = json.loads(before_lock_bytes)
before_inputs = {item["path"]: item["sha256"] for item in before_lock["records"]}
check("unchanged-ten-published-types-and-approved-Challenge", published_config == {
    "challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": PUBLISHED_EXPORTS,
    "definition_names": [], "permitted_axioms": STANDARD_AXIOMS}
    and challenge.count(intrinsic_import) == 1
    and challenge.replace(intrinsic_import, b"", 1).startswith(published_challenge)
    and sha(before_lock_bytes) == BEFORE_SOLUTION_LOCK_SHA256
    and len(before_inputs) == 70 and sha(challenge) == before_inputs["Challenge.lean"],
    published_export_count=len(PUBLISHED_EXPORTS), approved_boundary_lock_sha256=sha(before_lock_bytes))
check("unchanged-frozen-Reviewed-Infrastructure-and-Identity",
      source(PROJECT + "/Reviewed/TR06.lean") == source("lean-statements/Reviewed/TR06.lean", ORIGINAL_STATEMENT)
      and source(PROJECT + "/NLA/Statements/Infrastructure.lean") ==
          source("lean-statements/NLA/Statements/Infrastructure.lean", ORIGINAL_STATEMENT)
      and sha(source(PROJECT + "/Identity.lean")) == before_inputs["Identity.lean"],
      original_statement_commit=ORIGINAL_STATEMENT)

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
      and all(f"#assert_proof_constant {name}\n" in audit
              and f"#assert_trust kernel {name}\n" in audit for name in TARGETS),
      count=len(TARGETS))
trust_log = (logs / "leancert-proof-trust.log").read_text()
# Lean wraps long declaration names/axiom lists. Normalize only whitespace;
# require exactly one actual record per selected theorem and the exact three axioms.
axiom_records = parse_axiom_records(trust_log)
check("actual-export-standard-axioms", set(axiom_records) == set(TARGETS)
      and all(axiom_records[name] == [STANDARD_AXIOMS] for name in TARGETS),
      selected_export_count=len(TARGETS), observed=axiom_records)
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
      and "Artifact lean-TR-06 has been successfully uploaded!" in job_text)
archive_sha = sha(args.archive.read_bytes())
artifact_metadata = json.loads(args.artifact_metadata.read_text())
check("original-archive-matches-GitHub-digest", artifact_metadata["digest"] == "sha256:" + archive_sha,
      sha256=archive_sha)
check("original-archive-matches-job-upload", "SHA256 digest of uploaded artifact zip is " + archive_sha in job_text)
check("artifact-metadata-binds-run-and-head", artifact_metadata["workflow_run"]["id"] == metadata["databaseId"]
      and artifact_metadata["workflow_run"]["head_sha"] == args.ref and artifact_metadata["name"] == "lean-TR-06"
      and not artifact_metadata["expired"], artifact_id=artifact_metadata["id"])
with zipfile.ZipFile(args.archive) as archive:
    archived = {name: sha(archive.read(name)) for name in archive.namelist() if not name.endswith("/")}
downloaded = {str(p.relative_to(args.artifact)): sha(p.read_bytes())
              for p in args.artifact.rglob("*") if p.is_file()}
check("downloaded-extraction-equals-original-archive", archived == downloaded, file_count=len(archived))
if len(checks) != BASE_CONTROL_COUNT + ADDITIONAL_CONTROL_COUNT:
    raise RuntimeError("Strict control inventory changed unexpectedly")
report = {"schema_version": 1, "reviewer": args.reviewer,
          "inherited_control_count": BASE_CONTROL_COUNT,
          "additional_control_count": ADDITIONAL_CONTROL_COUNT,
          "expected_counts": EXPECTED_COUNTS,
          "actual_counts": {"selected_exports": len(config["theorem_names"]),
                            "canonical_Lean_inputs": sum(name.endswith(".lean") for name in result["input_sha256"]),
                            "copied_sources": len(copy_records), "proof_sources": proof_count,
                            "retained_sources": retained_count},
          "copy_records": copy_records, "retained_records": retained_records,
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
