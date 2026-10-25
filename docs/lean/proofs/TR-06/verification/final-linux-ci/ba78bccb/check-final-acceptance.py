#!/usr/bin/env python3
"""Bind actual TR06 proof/promotion/final receipts without editing canonical inputs."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re
import subprocess

BASE = Path(__file__).resolve().parent
VERIFICATION = BASE.parents[1]
REPO = BASE.parents[6]
PROJECT = "tensor-computations/TR-06/lean"
REF = "ba78bccb76fe219b7686cab9bca61b845636ad7a"
YAML_SHA = "b06badf047519b12c2b9ba1f1ce7c0b44b4a702eb6fb5f35f0b576e2c3af222f"
checks = []
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, default=BASE / "FINAL_ACCEPTANCE_2026-10-24.json",
                    help="Write a fresh aggregate replay here; use a separate file to preserve the retained acceptance")
args = parser.parse_args()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def check(name, passed, **evidence):
    checks.append({"name": name, "passed": bool(passed), **evidence})


stages = [
    ("proof", VERIFICATION / "linux-ci/2b049df5", "2b049df5e9b15318987f3fa592b1a7c65a0c0057", "2026-10-23"),
    ("promotion", VERIFICATION / "promotion-linux-ci/5a9f6eef", "5a9f6eefd2fc462144501a02a75cf313be4a09d7", "2026-10-23"),
    ("final", BASE, REF, "2026-10-24"),
]
chain = []
actuals = []
for label, directory, ref, date in stages:
    reports = []
    for reviewer in ["root", "independent"]:
        path = directory / f"{reviewer}-review-{date}.json"
        report = read(path)
        check(f"{label}:{reviewer}:actual-strict45", report["passed"]
              and report["source_commit"] == ref and len(report["checks"]) == 45
              and all(c["passed"] for c in report["checks"])
              and len(report["inputs"]) == 153)
        reports.append({"path": str(path.relative_to(REPO)), "sha256": sha(path),
                        "reviewer": report["reviewer"], "archive_sha256": report["archive_sha256"],
                        "artifact_id": report["artifact_id"]})
    result_path, = directory.glob("artifact/**/result.json")
    actual = read(result_path)
    actuals.append(actual)
    metadata = read(directory / "run-view.json")
    archive_path, = directory.glob("artifact-*.zip")
    check(label + ":actual-exact-push-artifact", metadata["event"] == "push"
          and metadata["status"] == "completed" and metadata["conclusion"] == "success"
          and metadata["headSha"] == actual["repository_commit"] == ref
          and actual["result"] == "comparator-accepted"
          and actual["lean_cert_proof_trust"] == "kernel-checked"
          and all(r["archive_sha256"] == sha(archive_path) for r in reports))
    chain.append({"stage": label, "source_commit": ref, "run": metadata["url"],
                  "replays": reports, "result_sha256": sha(result_path),
                  "archive_sha256": sha(archive_path)})

proof, promoted, final = [a["input_sha256"] for a in actuals]
check("exact153-input-sets-through-all-three-accepted-stages", len(final) == 153
      and proof.keys() == promoted.keys() == final.keys())
check("all144-Lean-input-bytes-identical-through-all-stages", sum(n.endswith(".lean") for n in final) == 144
      and all(proof[n] == promoted[n] == value for n, value in final.items() if n.endswith(".lean")))
check("promotion-only-README-and-YAML-final-only-three-label-YAML-input",
      {n for n in proof if proof[n] != promoted[n]} == {"README.md", "formalization.yaml"}
      and {n for n in promoted if promoted[n] != final[n]} == {"formalization.yaml"})
check("current-final153-bytes-still-exact", all(sha(REPO / PROJECT / n) == value for n, value in final.items()))
paths = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", "-z", REF, "--", PROJECT], cwd=REPO)
check("exact-final-committed153-path-set", {p.decode()[len(PROJECT)+1:] for p in paths.split(b"\0") if p} == set(final))
yaml = REPO / PROJECT / "formalization.yaml"
check("final-complete-proof-linux-verified-phase-and-reviewed-label-bytes", sha(yaml) == YAML_SHA
      and b"phase: complete-proof-linux-verified\n" in yaml.read_bytes()
      and b"whole_problem_verified: true\n" in yaml.read_bytes()
      and b"canonical_status: Lean verified\n" in yaml.read_bytes())
check("separate-final-boundary-and-IDs-observation-pass",
      read(BASE / "boundary-and-IDs/OBSERVATION_2026-10-24.json")["passed"])
failed = VERIFICATION / "linux-ci/8b714e1c/FAILED_ATTEMPT_OBSERVATION_2026-10-23.json"
check("earlier8b-failure-retained-without-acceptance", read(failed)["linux_proof_accepted"] is False
      and read(failed)["all_observational_checks_passed"])

campaign = REPO / "docs/lean/proofs/TR-06/campaign-2026-10-18/verification"
shared = read(campaign / "FULL_TARGET_80_APPROVAL_2026-10-23.json")
canonical = read(campaign / "CANONICAL_144_APPROVAL_2026-10-23.json")
check("fresh-shared80-and-canonical144-audits-accepted", shared["passed"] and canonical["passed"]
      and canonical["canonical_Lean_sources"] == 144 and canonical["explicit_declarations_checked"] == 772
      and canonical["theorem_kind_checks"] == 545 and canonical["negative_Challenge_rejections"] == 11)
promotion_review = VERIFICATION / "INDEPENDENT_PROMOTION_APPROVAL_2026-10-23.json"
label_review = VERIFICATION / "final-receipt-labels-2026-10-23/INDEPENDENT_REVIEW_2026-10-23.json"
check("concrete-promotion-and-exact-three-label-reviews-accepted", read(promotion_review)["passed"]
      and read(label_review)["passed"] and read(label_review)["after_sha256"] == YAML_SHA)
root_execution = BASE / "root-replay-execution-2026-10-25.json"
check("separate-final-root-replay-and-actual-execution-record-bound",
      sha(BASE / "root-review-2026-10-24.json") == "4046d52bb76ee99c08749f169311701de19ed7a02d9de08d2c83ea43c0a8f12e"
      and root_execution.is_file())
registry_path = REPO / "problem_ids.json"
registry = read(registry_path)
original_registry = subprocess.check_output(["git", "show", stages[0][2] + ":problem_ids.json"], cwd=REPO)
check("all217-permanent-ID-path-pairs-unchanged", len(registry) == 217
      and registry["TR-06"] == "tensor-computations/TR-06/README.md"
      and registry_path.read_bytes() == original_registry)
other_pages = []
for identifier, path in registry.items():
    if identifier != "TR-06":
        data = (REPO / path).read_bytes()
        original = subprocess.check_output(["git", "show", stages[0][2] + ":" + path], cwd=REPO)
        other_pages.append({"id": identifier, "path": path, "sha256": hashlib.sha256(data).hexdigest(),
                            "passed": data == original})
check("all216-other-canonical-problem-pages-unchanged", len(other_pages) == 216
      and all(r["passed"] for r in other_pages))
canonical_readme = (REPO / registry["TR-06"]).read_bytes()
restored_readme, notices = re.subn(
    rb"\n<!-- lean-tr06-complete-2026-10-23 -->\n.*?<!-- /lean-tr06-complete-2026-10-23 -->\n",
    b"", canonical_readme, flags=re.S)
restored_readme = restored_readme.replace(b"**Status:** Lean verified  \n", b"**Status:** Solved  \n", 1)
restored_readme = restored_readme.replace(b"**Last checked:** 2026-10-23  \n", b"**Last checked:** 2026-09-11  \n", 1)
check("original-TR06-mathematical-page-still-byte-recoverable", notices == 1
      and restored_readme == subprocess.check_output(
          ["git", "show", stages[0][2] + ":" + registry["TR-06"]], cwd=REPO))
archive_manifest = read(REPO / "docs/lean/proofs/TR-06/originals-c4c7be59/manifest.json")
check("all-five-original-archives-still-exact", len(archive_manifest["records"]) == 5
      and archive_manifest["base_ref"] == "c4c7be592c51c8ba81d1579082813310a22b356d"
      and all(sha(REPO / r["archive"]) == r["sha256"]
              and (REPO / r["archive"]).read_bytes() == subprocess.check_output(
                  ["git", "show", archive_manifest["base_ref"] + ":" + r["source"]], cwd=REPO)
              for r in archive_manifest["records"]))

report = {"receipt_batch_date": "2026-10-24", "finalization_execution_UTC": datetime.datetime.now(datetime.timezone.utc).isoformat(),
          "reviewer": "/root/recover_verification (independent non-proof-author Codex AI agent)",
          "scope": "Final immutable TR06 exact-statement, proof, canonical source, actual Linux Comparator/kernel and original-preservation acceptance chain",
          "passed": all(c["passed"] for c in checks), "checks": checks,
          "final_source_commit": REF, "final_metadata_phase": "complete-proof-linux-verified",
          "canonical_status": "Lean verified", "canonical_inputs": 153, "canonical_Lean_inputs": 144,
          "source_copies": 140, "completion_proof_modules": 80, "retained_original_modules": 58,
          "selected_exports": 11, "permitted_and_actual_axioms": ["propext", "Classical.choice", "Quot.sound"],
          "actual_CI_acceptance_chain": chain,
          "fresh_shared80_approval_sha256": sha(campaign / "FULL_TARGET_80_APPROVAL_2026-10-23.json"),
          "fresh_canonical144_approval_sha256": sha(campaign / "CANONICAL_144_APPROVAL_2026-10-23.json"),
          "concrete_promotion_approval_sha256": sha(promotion_review),
          "final_three_label_review_sha256": sha(label_review), "earlier_failed_attempt_sha256": sha(failed),
          "separate_root_final_replay_execution_sha256": sha(root_execution),
          "current_other216_page_records": other_pages,
          "independent_final_direct_approval_sha256": sha(BASE / "INDEPENDENT_FINAL_LINUX_APPROVAL_2026-10-24.json"),
          "final_input_sha256": final, "acceptance_driver_sha256": sha(Path(__file__)),
          "all_Solved_campaign_complete": False,
          "limitations": ["The acceptance is bound to the exact frozen153 canonical input hashes. Later evidence/PR description updates stay outside canonical inputs.",
                          "Retained artifact replays do not claim another local Linux execution.",
                          "All reviews are AI-agent work; no external human endorsement is claimed.",
                          "The broader all-Solved campaign remains active."]}
args.output.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"passed": report["passed"], "controls": len(checks),
                  "failed_controls": [c["name"] for c in checks if not c["passed"]]}, indent=2))
raise SystemExit(0 if report["passed"] else 1)
