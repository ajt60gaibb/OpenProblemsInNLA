#!/usr/bin/env python3
"""Audit retained full IE-21 Linux evidence; does not rerun Lean or review mathematics."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import re
import tarfile

base = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads((base / p).read_text())
permitted = {"propext", "Classical.choice", "Quot.sound"}
publication = "1eb284b84ecc0d3c958d022b3e020be7fa111391"
guest_commit = "bd72d630841a1660b9f7652d469186c11728925f"
input_receipt = read("input-receipt.json")
preparation = read("preparation.json")
runner = read("runner-result-attempt-1.json")
result = read("successful-verification/result.json")
bootstrap = read("bootstrap.json")
export = read("evidence-export-receipt.json")
dependencies = read("dependency-evidence/dependency-receipt.json")
provenance = read("execution-provenance.json")

assert sha(base / "input.tar") == input_receipt["archive_sha256"] == \
    "6b61efee12a30cde167f1e2ac22b1b0662be0324475e37b222e3cd8ee466c6dd"
assert (base / "input.tar").stat().st_size == input_receipt["archive_bytes"] == 1228800
assert sha(base / "verification-evidence.tar.gz") == export["sha256"]
assert (base / "verification-evidence.tar.gz").stat().st_size == export["bytes"]
assert input_receipt["publication_commit"] == preparation["publication_commit"] == publication
assert result["repository_commit"] == preparation["guest_repository_commit"] == guest_commit
assert guest_commit != publication
assert sha(base / "input-receipt.json") == preparation["receipt_sha256"]
assert result["project"] == input_receipt["project_path"] == "linear-systems-and-elimination/IE-21/lean"

source = base / "source"
hashes = {str(p.relative_to(source)): sha(p) for p in source.rglob("*") if p.is_file()}
assert len(hashes) == len(input_receipt["input_sha256"]) == preparation["tracked_input_count"] == 289
assert hashes == input_receipt["input_sha256"] == preparation["input_sha256"]
assert hashes == result["input_sha256"] == dependencies["snapshot_input_sha256"]
with tarfile.open(base / "input.tar") as archive:
    extracted = {}
    for item in archive.getmembers():
        assert item.isdir() or item.isfile(), item.name
        path = PurePosixPath(item.name)
        assert not path.is_absolute() and ".." not in path.parts, item.name
        if item.isfile():
            relative = str(path.relative_to(result["project"]))
            assert relative not in extracted
            extracted[relative] = hashlib.sha256(archive.extractfile(item).read()).hexdigest()
    assert extracted == hashes
with tarfile.open(base / "verification-evidence.tar.gz") as archive:
    for item in archive.getmembers():
        assert item.isdir() or item.isfile(), item.name
        path = PurePosixPath(item.name)
        assert not path.is_absolute() and ".." not in path.parts, item.name
        if item.isfile():
            assert (base / path).read_bytes() == archive.extractfile(item).read(), item.name

assert preparation["git_status"] == provenance["git_status_after_verification"] == ""
assert preparation["prior_project_build_artifacts"] is False
assert provenance["all_inputs_unchanged_after_verification"] is True
assert provenance["failed_verification_attempts"] == 0
assert provenance["host_preparation_issues_before_verification"] == 1
assert preparation["uid"] == provenance["uid"] == 1000
assert runner["status"] == "finished" and runner["exit_code"] == 0
assert runner["command"] == ["/home/admin/mf21-harness/tools/lean/verify.sh",
    "linear-systems-and-elimination/IE-21/lean", "/home/admin/nla-lean-tools"]
assert result["result"] == provenance["result"] == "comparator-accepted"

config = result["config"]
assert config == json.loads((source / "comparator.json").read_text())
names = input_receipt["theorem_names"]
assert len(names) == len(set(names)) == preparation["selected_theorem_count"] == 23
assert config["theorem_names"] == names
assert config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution"
assert config.get("definition_names", []) == []
assert set(config["permitted_axioms"]) == permitted
challenge_names = ["NLA.IE21." + n for n in re.findall(
    r"^theorem ([A-Za-z_][A-Za-z_0-9]*)", (source / "Challenge.lean").read_text(), re.M)]
assert challenge_names == names
solution = (source / "Solution.lean").read_text()
assert 'import LeanCert.Tactic.Verification' in solution
assert 'set_option leancert.trust "kernel"' in solution
assert re.findall(r"^#assert_trust kernel (\S+)$", solution, re.M) == names
assert re.findall(r"^#print axioms (\S+)$", solution, re.M) == names
assert "import Challenge" not in solution
freeze = json.loads((source / "reviews/package-source-freeze.json").read_text())
assert sha(source / "reviews/package-source-freeze.json") == input_receipt["package_source_freeze_sha256"] == "b4ab97645ec9f8c46c7130aabc4bac48cbab48af0c96d4f454ad58c32a981744"
assert len(freeze["source_sha256"]) == 41
for name, digest in freeze["source_sha256"].items():
    assert hashes[name] == digest, name
correctness = json.loads((source / "reviews/ie21-final-correctness-evidence/final-source-review-receipt.json").read_text())
fidelity = json.loads((source / "reviews/ie21-final-fidelity-evidence/review-receipt.json").read_text())
assert correctness["source_package_sha256"] == fidelity["reviewed_package_sha256"] == freeze["source_sha256"]
assert correctness["package_freeze_sha256"] == fidelity["package_freeze_sha256"] == input_receipt["package_source_freeze_sha256"]

assert result["tool_receipt"] == bootstrap
assert result["source_lock_sha256"] == bootstrap["source_lock_sha256"] == \
    sha(base / "checker-source/source-lock.json")
assert bootstrap["forsythe_commit"] == "8d1b0c0545a77b40245e84705aa7d273e6c81e62"
assert bootstrap["lean_toolchain"] == "leanprover/lean4:v4.33.1"
assert bootstrap["env_sha256"] == sha(base / "checker-runtime-source/env.sh")
assert bootstrap["ci_sandbox_probe_sha256"] == sha(base / "checker-runtime-source/sandbox_probe_ci.py")
preflight = read("prerequisite-inspection.json")
assert preflight["validated_tools"] == "PASS" and preflight["tool_receipt"] == bootstrap
for name, digest in preflight["driver_sha256"].items():
    assert sha(base / "checker-source" / name) == digest, name
manifest = json.loads((source / "lake-manifest.json").read_text())
pins = {p["name"]: p["rev"] for p in manifest["packages"]}
assert len(pins) == 10
assert pins["mathlib"] == "0df444a360eaa60ab8c11dca51a86af692955474"
assert pins["leancert"] == "621a43d7cf21f87872392a01e874f2f1dbddc926"
assert {p["name"]: p["actual_git_head"] for p in dependencies["packages"]} == pins
assert dependencies["package_heads_all_match_manifest"] is True
assert dependencies["LeanCert_Verification_bytes_match_pinned_git_blob"] is True
assert dependencies["LeanCert_Verification_sha256"] == \
    sha(base / "dependency-evidence/LeanCert-Verification.lean") == \
    "2c576708b528acdde17796b0b715b83079f9cad377182dbd87c248323ff0a58c"

logs = {p.name: p.read_text() for p in (base / "successful-verification").glob("*.log")}
for name in ["user-service.log", "sandbox.log", "kernel-controls.log", "comparator-controls.log",
             "dependencies.log", "mathlib-cache.log", "comparator.log"]:
    assert logs[name].rstrip().endswith("EXIT_STATUS=0"), name
sandbox = logs["sandbox.log"]
for marker in ["MODE build: exit=0", "MODE export: exit=0", "PASS build .lake write: allowed",
               "PASS export .lake write-open: denied", "PASS export .lake truncate: denied",
               "Outer and export fixture contents unchanged; only designated build fixture written."]:
    assert marker in sandbox, marker
for marker in ["PASS outside .lake write-open: denied", "PASS outside .lake truncate: denied",
               "PASS outside .lake read-only truncate-open: denied", "PASS outside .lake creation: denied",
               "PASS symlink from .lake to outside write: denied", "PASS user namespace: private",
               "PASS pid namespace: private", "PASS mnt namespace: private", "PASS net namespace: private",
               "PASS ipc namespace: private", "PASS uts namespace: private",
               "PASS host parent: absent from private /proc", "PASS host parent signal lookup: denied",
               "PASS AF_UNIX socket creation: denied", "PASS host loopback listener: unreachable",
               "PASS effective capabilities: none", "PASS no_new_privs: set", "Sandbox UID: 1000",
               "PASS nested namespace write attempt: rejected exit=1",
               "bwrap: setting up uid map: Permission denied"]:
    assert sandbox.count(marker) == 2, marker
for case in ["unknown option", "unexpected --rw", "unexpected --rwx", "relative --rwx"]:
    assert "NEGATIVE " + case + ": exit=2" in sandbox
for marker in ["RETURN honest_with_inductives_and_quotients: accepted",
               "RETURN invalid_raw_proof: rejected: while replaying declaration",
               "RETURN quotient_postcheck_mismatch: rejected: Quotient constant mismatch on: Quot.lift",
               "PASS: all three actual Comparator.runBuiltinKernel cases behaved as required"]:
    assert marker in logs["kernel-controls.log"], marker
for case in ["simple_match", "simple_mismatch", "simple_axiom_issue", "simple_kind_mismatch", "type_mismatch"]:
    assert "PASS " + case + ":" in logs["comparator-controls.log"], case
assert "PASS: all five Comparator regressions" in logs["comparator-controls.log"]
for name, marker in [("negative-sorry.log", "Illegal axiom detected: 'sorryAx'"),
                     ("negative-native.log", "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'")]:
    assert marker in logs[name] and logs[name].rstrip().endswith("EXIT_STATUS=1"), name

proof = logs["comparator.log"]
assert proof.index("Building Challenge") < proof.index("from Challenge") < proof.index("Building Solution")
assert "Built LeanCert.Tactic.Verification" in proof and "Built Solution" in proof
assert "Running Lean default kernel on solution." in proof
assert "Lean default kernel accepts the solution" in proof and "Your solution is okay!" in proof
exports = re.findall(r"^Exporting #\[(.*)\] from (Challenge|Solution)$", proof, re.M)
assert [module for _, module in exports] == ["Challenge", "Solution"]
for declarations, module in exports:
    assert [n for n in declarations.split(", ") if n.startswith("NLA.IE21.")] == names, module
reports = re.findall(r"^info: Solution\.lean:\d+:\d+: '([^']+)' depends on axioms: \[([^]]+)\]$", proof, re.M)
assert [name for name, _ in reports] == names
assert all(set(axioms.split(", ")) == permitted for _, axioms in reports)
assert len(re.findall(r"^warning: Challenge\.lean:.*declaration uses `sorry`$", proof, re.M)) == len(names)
assert not re.search(r"^warning: (?!Challenge\.lean:)|^error:", proof, re.M)
assert "No files to download" in logs["mathlib-cache.log"], "Inspect/cache-download provenance before changing this expected retained-cache assertion"

print("PASS: exact input/evidence archives, all 289 source files and distinct commit provenance")
print("PASS: all 10 pinned dependency heads, authentic LeanCert verification source and pinned checker receipts")
print("PASS: all real sandbox, raw-kernel, Comparator and forbidden-axiom controls")
print("PASS: all 23 reviewed declarations exported separately and matched by Comparator")
print("PASS: authentic LeanCert kernel assertions compiled; every exported theorem uses only the three standard axioms")
print("PASS: actual Lean kernel accepted the complete IE-21 solution; verifier EXIT 0")
print("ROLE: mechanical evidence audit, not independent mathematical peer review")
