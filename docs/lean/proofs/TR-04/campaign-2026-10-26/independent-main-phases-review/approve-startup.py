#!/usr/bin/env python3
"""Accept only the completed startup scope of the retained partial batch."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
BASE = Path(__file__).resolve().parent
REPO = BASE.parents[5]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
ref = lambda p: {"path": str(p.relative_to(REPO)), "sha256": sha(p)}
run = BASE / "run-attempt-1"
rp = run / "result.json"
r = json.loads(rp.read_text())
b = json.loads((BASE / "source-lock.json").read_text())["blocks"][0]
v = r["blocks"]["startup"]
assert r["passed"] is False and v["passed"] is True
assert v["project_closure_count"] == 41 and v["explicit_named_declarations"] == 515
assert v["actual_name_bindings_passed"] and v["literal_examples"] == 10
assert len(v["owned_declarations"]) == 44 and v["actual_owned_kernel_theorem_count"] == 39
assert len(v["private_or_local_named_declarations"]) == 28
assert r["driver_sha256"] == sha(BASE / "replay-attempt-1.py")
assert r["source_lock_sha256"] == sha(BASE / "source-lock.json")
assert sha(REPO / b["author_lock_path"]) == b["author_lock_sha256"]
assert all(x["passed"] for k in ["dependencies_before", "dependencies_after", "original25_before", "original25_after"] for x in r[k])
assert all(r["source_unchanged_after"].values()) and all(r["author_locks_unchanged_after"].values())
assert v["observed_axioms"] == ["Classical.choice", "Quot.sound", "propext"]
commands = {c["source"]: c for c in r["commands"]}
for record in b["records"]:
    name = record["path"].removeprefix("lean-statements/")
    assert commands[name]["exit_code"] == 0
    assert sha(REPO / record["path"]) == record["sha256"] == sha(run / "sources" / name)
for c in r["commands"][:42]:
    assert c["exit_code"] == 0 and sha(run / c["log"]) == c["log_sha256"]
author_result = BASE.parent / "tt-startup-author/result.json"
assert sha(author_result) == "fade3d6df55347ebafdab97ac4c01a816f3252d9911f93ca89caaccdec7bd76f"
assert json.loads(author_result.read_text())["passed"]
a = {"passed": True, "approval": "APPROVED_FROZEN_STARTUP_PHASE_ONLY",
    "reviewer": "/root/recover_verification", "proof_source_authorship": [],
    "recorded_utc": datetime.now(timezone.utc).isoformat(), "author": b["author"],
    "author_source_lock": {"path": b["author_lock_path"], "sha256": b["author_lock_sha256"]},
    "author_terminal_result": ref(author_result), "retained_partial_batch_result": ref(rp),
    "aggregate_batch_passed": False, "scoped_kernel_result": v,
    "source_review": [
        "The complete frozen startup body was read, including all28 explicit private helper theorems. Its 25 actual instructions119..143 execute in6/6/7/6 segments, compute the literal layout pointers by natural arithmetic and leave all old tensor memory unchanged.",
        "Entry requires actual pc119/running, natural0=order, natural2=entries and natural127=0. The decoded first mode is not preloaded: instruction138 actually reads memory0 into real0. The entry equation memory0=(value:Real) is a literal memory-cell condition, not an evaluation or result premise.",
        "The actual all-legal-trace endpoint reaches installed header decoder label5, with cursor=order, product1, counter0 and first-mode real input, plus all TTAllocationRegisters and zero candidate/tag1 flags. Prefix charge increases by at most25.",
        "All15 author-selected public declarations, the additional named NeZero proof instance and all28 explicit private helpers receive exact actual kind/kernel/axiom checks. Private names use Lean.mkPrivateNameCore with the exact frozen module and name; every binding is retained. The source transparency option affects elaboration only.",
        "Ten complete public theorem headers and an independent composed actual startup-read to installed Single-decoder consumer pass. That consumer returns running at label10 with actual decoded natural2=value, full old memory, and prefix charge plus25+(3*value+5)."
    ],
    "freshness": "All41 source-bound project prerequisites rebuilt into an empty private root and the startup consumer completed as command42 before the later metadata consumer failed. No previous project objects reused; pinned external package objects reused.",
    "kernel_mode": "LeanCert kernel", "axioms": v["observed_axioms"],
    "authored_source_files": 1, "author_selected_public_declarations": 15,
    "all_explicit_authored_names": 44, "explicit_private_helpers": 28,
    "actual_authored_kernel_theorems_including_private_and_instance": 39,
    "literal_endpoint_examples": 10, "additional_actual_decoder_composition_examples": 1,
    "private_name_provenance": ref(BASE / "private-name-provenance.json"),
    "auditor_control_result": ref(BASE / "private-auditor-preflight-2/result.json"),
    "consumer": {"path": str((run / "sources/Independent_startup_Consumer.lean").relative_to(REPO)), "sha256": r["consumer_sha256"]["Independent_startup_Consumer.lean"]},
    "later_batch_failure": "The metadata consumer could not elaborate some unchanged numeral register types without its source's named local instance activated. Startup is independently terminal and accepted; the batch remains false and FirstSelection was not yet built.",
    "limits": "Startup/first-memory-read/decoder-entry and this composed Single-decoder prefix only. Full initializer dispatch, first SVD reachability, later recursion, approximation, total cost, literal Target and authoritative Linux/Comparator remain separate.",
    "ten_exact_clean_pins_before_after": True, "original25_byte_exact_against_2b_before_after": True,
    "proof_inputs_changed": False, "full_TR04_Target_proved": False, "authoritative_Linux_Comparator": False}
p = BASE / "APPROVAL-startup.json"
p.write_text(json.dumps(a, indent=2) + "\n")
print(json.dumps({"passed": True, "approval": ref(p), "retained_aggregate_passed": False}, indent=2))
