#!/usr/bin/env python3
"""Bind the terminal independent Dimension2 kernel replay, without modifying inputs."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[5]


def sha(p):
    assert p.is_file() and not p.is_symlink(), str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()


def ref(p):
    return {"path": str(p.relative_to(REPO)), "sha256": sha(p)}


run = BASE / "run-attempt-2"
rp = run / "result.json"
r = json.loads(rp.read_text())
lock = json.loads((BASE / "source-lock.json").read_text())
b = lock["blocks"][0]
v = r["blocks"]["dimensions"]
assert r["passed"] and r["project_sources"] == 27 and len(r["commands"]) == 28
assert v["passed"] and v["all_named_declaration_checks_passed"]
assert v["project_closure_count"] == 27 and v["owned_source_count"] == 2
assert len(v["owned_declarations"]) == 31 and v["actual_owned_kernel_theorem_count"] == 27
assert v["literal_examples"] == 27
assert v["observed_axioms"] == ["Classical.choice", "Quot.sound", "propext"]
assert r["driver_sha256"] == sha(BASE / "replay.py")
assert r["inventory_sha256"] == sha(BASE / "source_inventory.py")
assert r["source_lock_sha256"] == sha(BASE / "source-lock.json")
assert sha(REPO / b["author_lock_path"]) == b["author_lock_sha256"]
assert r["lean_sha256"] == "1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554"
assert not r["project_objects_reused"] and r["pinned_external_dependency_objects_reused"]
assert all(v["passed"] for k in ["dependencies_before", "dependencies_after", "original25_before", "original25_after"] for v in r[k])
assert all(r["source_unchanged_after"].values()) and all(r["author_locks_unchanged_after"].values())
assert not r["private_or_local_named_declarations"]
failed_run = BASE / "run-attempt-1"
failed = json.loads((failed_run / "result.json").read_text())
assert failed["passed"] is False
assert [(c["source"], c["exit_code"]) for c in failed["commands"] if c["exit_code"]] == [("Independent_dimensions_Consumer.lean", 1)]
assert sha(BASE / "replay.py") == failed["driver_sha256"]
for c in failed["commands"]:
    assert sha(failed_run / c["log"]) == c["log_sha256"]
for name, digest in {**failed["source_sha256"], **failed["consumer_sha256"]}.items():
    assert sha(failed_run / "sources" / name) == digest
for name, digest in r["source_sha256"].items():
    assert sha(run / "sources" / name) == digest
    assert sha(REPO / "lean-statements" / name) == digest
for name, digest in r["consumer_sha256"].items():
    assert sha(run / "sources" / name) == digest
for c in r["commands"]:
    assert c["exit_code"] == 0 and sha(run / c["log"]) == c["log_sha256"]
history = json.loads((BASE / "author-history.json").read_text())
assert history["passed"] and not history["interrupted_run_accepted"]
assert not history["interrupted_run_terminal_result_present"]
assert history["source_snapshot_count_each"] == 27
for name, digest in history["artifact_hashes"].items():
    assert sha(REPO / name) == digest

approval = {
    "passed": True,
    "approval": "APPROVED_FROZEN_RECURSIVE_DIMENSION_COMPONENT_ONLY",
    "reviewer": "/root/recover_verification", "proof_source_authorship": [],
    "recorded_utc": datetime.now(timezone.utc).isoformat(),
    "execution_started_utc": r["started_utc"], "execution_finished_utc": r["finished_utc"],
    "author": b["author"],
    "author_source_lock": {"path": b["author_lock_path"], "sha256": b["author_lock_sha256"]},
    "independent_source_lock": ref(BASE / "source-lock.json"), "result": ref(rp),
    "scoped_kernel_result": v,
    "source_review": [
        "Both frozen bodies were read, together with the exact stepRank/stepInput and originalRanks definitions. stepRank is the actual minimum of the requested rank, rows and suffix cardinality. The child format ((stepRank*mNext)::tail) and level-shifted rank profile are exactly the frozen stepInput type, independently of the chosen matrix or tensor values.",
        "For all natural dimensions and requested ranks, including zero, the child dense product and contracted dense count do not exceed the parent product. Positivity is used only in the positive-rank branch. The rank profile requires positivity solely at actual current cuts j+1<length; unused zero-extended original ranks are never assumed positive.",
        "Reachable contains only start and the exact recursive format transition. It contains no assumed size or capacity bound. Induction proves positive current modes and actual cut ranks, current dense product<=original dense product, and current length+level=original length. Its remaining tail equals original.drop(level+1), including terminal one-mode formats.",
        "The original bridge uses the unchanged Shape mode lower bounds and actual finite prescribed ranks>=1. It derives actual rows/columns/capped rank/child-mode positivity and bounds, parent dense m*cols<=N, contracted q*cols<=N, child dense<=N, and m^2/m*q/cols^2<=N^2. Dense work capacities are conclusions here, not premises in the original reachable theorem.",
        "All27 explicit authored theorem headers compile verbatim. Three additional consumers project the complete original N-cell/N^2 capacity package using only original rank positivity and Reachable; prove actual child Index cardinality nonincrease without positivity assumptions; and retain the zero requested-rank case."
    ],
    "limits": "Dimension arithmetic of the exact recursive format only. A program state must still be related to this Reachable format and its actual memory/register representation. Full recursive execution, approximation correctness, uniform total charged cost, literal Target, authoritative Linux and Comparator acceptance remain separate.",
    "freshness": "All27 source-bound project prerequisites rebuilt into an empty private object root before the separate consumer. No prior project objects reused; exact pinned external package objects reused.",
    "kernel_mode": "LeanCert kernel", "axioms": v["observed_axioms"],
    "authored_source_files": 2, "authored_named_declarations": 31,
    "authored_actual_kernel_theorems": 27, "literal_endpoint_examples": 27,
    "additional_independent_examples": 3,
    "integration_examples": ref(BASE / "integration-dimensions.lean.txt"),
    "author_interrupted_and_final_history": ref(BASE / "author-history.json"),
    "interrupted_author_attempt_accepted": False,
    "ten_exact_clean_pins_before_after": True, "original25_byte_exact_against_2b_before_after": True,
    "private_or_local_explicit_declarations": [],
    "generated_declaration_scope": "Explicit source names receive exact kind/kernel/axiom checks; compilation and transitive axiom auditing cover generated and anonymous helpers without claiming separate explicit-name checks.",
    "reproducers": [ref(BASE / n) for n in ["prepare.py", "replay.py", "source_inventory.py", "check-author-history.py", "make-approval.py"]],
    "retained_failed_independent_Lean_attempts": [{"result": ref(failed_run / "result.json"), "diagnostic": ref(BASE / "cardinality-consumer-diagnostic.json"), "initial_integration": ref(BASE / "integration-dimensions-attempt-1.lean.txt"), "accepted": False}],
    "proof_inputs_changed": False, "full_TR04_Target_proved": False, "authoritative_Linux_Comparator": False,
}
p = BASE / "APPROVAL.json"
p.write_text(json.dumps(approval, indent=2) + "\n")
print(json.dumps({"passed": True, "approval": ref(p), "result": ref(rp)}, indent=2))
