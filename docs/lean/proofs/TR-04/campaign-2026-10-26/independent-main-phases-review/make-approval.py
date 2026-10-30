#!/usr/bin/env python3
"""Bind complete private fresh phase replay plus the retained partial startup receipt."""
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
config = json.loads((BASE / "source-lock.json").read_text())
assert r["passed"] and r["project_sources"] == 100 and len(r["commands"]) == 103
assert len(r["declarations"]) == 1028
assert r["driver_sha256"] == sha(BASE / "replay.py")
assert r["inventory_sha256"] == sha(BASE / "source_inventory.py")
assert r["source_lock_sha256"] == sha(BASE / "source-lock.json")
assert r["private_name_provenance_sha256"] == sha(BASE / "private-name-provenance.json")
assert len(config["private_name_map"]) == 62
assert len(r["private_or_local_named_declarations"]) == 63
assert r["lean_sha256"] == "1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554"
assert not r["project_objects_reused"] and r["pinned_external_dependency_objects_reused"]
assert all(v["passed"] for k in ["dependencies_before", "dependencies_after", "original25_before", "original25_after"] for v in r[k])
assert all(r["source_unchanged_after"].values()) and all(r["author_locks_unchanged_after"].values())
for name, digest in r["source_sha256"].items():
    assert sha(run / "sources" / name) == digest
    assert sha(REPO / "lean-statements" / name) == digest
for name, digest in r["consumer_sha256"].items(): assert sha(run / "sources" / name) == digest
for c in r["commands"]: assert c["exit_code"] == 0 and sha(run / c["log"]) == c["log_sha256"]
for b in config["blocks"]:
    assert sha(REPO / b["author_lock_path"]) == b["author_lock_sha256"]
    assert r["blocks"][b["key"]]["passed"] and r["blocks"][b["key"]]["actual_name_bindings_passed"]
    assert r["blocks"][b["key"]]["observed_axioms"] == ["Classical.choice", "Quot.sound", "propext"]
oldrun = BASE / "run-attempt-1"
failed = json.loads((oldrun / "result.json").read_text())
assert failed["passed"] is False and failed["blocks"]["startup"]["passed"]
assert [(c["source"], c["exit_code"]) for c in failed["commands"] if c["exit_code"]] == [("Independent_dispatch_metadata_Consumer.lean", 1)]
assert failed["driver_sha256"] == sha(BASE / "replay-attempt-1.py")
assert failed["source_lock_sha256"] == r["source_lock_sha256"]
assert failed["source_sha256"] == r["source_sha256"]
for key in r["consumer_bindings"]:
    assert failed["consumer_bindings"][key]["literal_examples"] == r["consumer_bindings"][key]["literal_examples"]
for c in failed["commands"]: assert sha(oldrun / c["log"]) == c["log_sha256"]
for name, digest in {**failed["source_sha256"], **failed["consumer_sha256"]}.items(): assert sha(oldrun / "sources" / name) == digest
history = json.loads((BASE / "author-and-control-receipts.json").read_text())
assert history["passed"] and len(history["terminal_author_results"]) == 3
assert history["private_auditor_positive_and_negative_passed"]
assert not history["negative_custom_axiom_fixture_accepted_as_proof"]
for name, digest in history["artifact_hashes"].items(): assert sha(REPO / name) == digest
control = json.loads((BASE / "private-auditor-preflight-4/result.json").read_text())
assert control["driver_sha256"] == r["driver_sha256"] and control["passed"]
startup = BASE / "APPROVAL-startup.json"
assert sha(startup) == "d9a4bc574ee65541508d2c778df3f53d91d1f3ba8d5fff34e87a6588c4d2aeb2"
assert json.loads(startup.read_text())["passed"]

reviews = {
    "dispatch_metadata": {
        "expected": (39, 2, 39, 31, 30),
        "approval": "APPROVED_FROZEN_ACTUAL_HEADER_DISPATCH_AND_METADATA_PHASES_ONLY",
        "source_review": [
            "Both full frozen bodies were read. Header dispatch executes the actual jump at10 and literal natural/equalNat pairs at372..393. For each actual tag k:Fin11, it reaches the fixed handler after2*k+3 steps, preserves all real registers and memory, and changes only natural123. The complete handler map and all rejection/acceptance steps are proved from literal code equality.",
            "Metadata executes actual instructions241..254: two address setup instructions and four cast/write/increment triples. It reaches255 after14 steps, stores exact casts of the old natural85/86/87/88 values in metadata+4*level+field, advances natural93 by4, and preserves all memory outside those four cells, every natural register except93, and every real register except13.",
            "Metadata entry assumes only the stated actual pc/running and natural68=metadata, natural125=4, natural84=level fields. Its finite-prefix memory helper is a proved poststate of the actual instructions, not an evaluation or result premise. Every legal trace at every offset carries the actual prefix-charge bound.",
            "All38 author-selected public declarations plus the named local NeZero proof instance receive exact kind/kernel/axiom checks. The consumer reactivates this exact audited source-local instance before elaborating the unchanged numeral instruction types. All30 complete public theorem headers pass, plus actual tag0/tag10 handler/cost tests and four concrete metadata-cell cast projections."
        ],
        "limits": "Valid finite tag0..10 dispatch and actual four-cell metadata writes only. The caller must establish the valid tag and relate the level/address to its reserved allocation when memory safety is needed. Complete initialization, later matrix/gather/recursive phases, approximation, total global cost and full Target/authoritative CI acceptance remain separate.",
        "additional_examples": 3,
    },
    "first_selection": {
        "expected": (93, 6, 78, 65, 30),
        "approval": "APPROVED_FROZEN_ACTUAL_FIRST_SVD_SELECTION_PHASE_ONLY",
        "source_review": [
            "All six complete frozen bodies were read, including34 explicit private scalar-code/register helpers. The phase uses the actual fixed program167 SVD response, followed by scalar branches and the installed read-only threshold scan. The received full rectangular U/sigma/V tuple comes from the given legal trace; no favorable later reply or comparator is selected.",
            "At actual return168, requested rank>min(rows,cols) takes the six-step prefix path. Otherwise it really reads sigma[r-1] and compares it against the cast of actual zero127. A nonpositive threshold takes the twelve-step prefix path. A positive threshold runs the literal count bank and stores actual above/tied/take/count fields before entering189 after9*p+23 steps.",
            "The prefix route stores above=capped rank, tied1, take0, count1. The positive route stores the exact counted complete threshold block. The resulting count is positive and width above+take equals the literal capped rank, including empty-dimension prefix fallback. Natural memory/pointer/global preservation is exactly TTFirstProtected (indices>=49 excluding75/77/78/79/122); no blanket real-register preservation is claimed.",
            "The SVD endpoint retains post-SVD writeSVD memory and actual U/sigma/V readbacks. It reaches running189 with time<=9*p+24 and actual charged prefix increment<= (rows+cols+1)^3+9*p+23. Its entry retains actual p/rank/cap/zero register equations and literal OutputBlocksDisjoint; establishing them from original Start belongs to the separate initializer.",
            "TTFirstChoiceRealizes proves that the actual selected index/count/width parameters realize the exact frozen explicitFirstFrames family through literal gather-matrix columns, with value-preserving index casts, for every legal full decomposition. This is a mathematical parameter/column bridge; actual runtime gathering after189 is a later phase.",
            "All44 author-listed public declarations and34 private helpers receive exact actual-kind/kernel/axiom checks. All30 complete public theorem headers pass. An additional independent all-legal-trace consumer derives actual natural75>0 and natural77+natural79=capped rank from ttFirstSelection_svd_family, preserving the same actual charge bound."
        ],
        "limits": "Actual first-SVD/threshold-selection phase and exact explicit-family parameter realization only. Runtime gathering/storage of frames, all children and comparators, return tensor correctness, full uniform execution and total polynomial cost remain separate. No literal Target, authoritative Linux or Comparator acceptance claim.",
        "additional_examples": 1,
    },
}
receipts = [ref(startup)]
for b in config["blocks"]:
    if b["key"] == "startup": continue
    key = b["key"]
    d = reviews[key]
    v = r["blocks"][key]
    closure, files, names, theorems, examples = d["expected"]
    assert v["project_closure_count"] == closure and v["owned_source_count"] == files
    assert len(v["owned_declarations"]) == names and v["actual_owned_kernel_theorem_count"] == theorems
    assert v["literal_examples"] == examples
    a = {"passed": True, "approval": d["approval"], "reviewer": "/root/recover_verification",
        "proof_source_authorship": [], "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "execution_started_utc": r["started_utc"], "execution_finished_utc": r["finished_utc"],
        "author": b["author"], "author_source_lock": {"path": b["author_lock_path"], "sha256": b["author_lock_sha256"]},
        "independent_source_lock": ref(BASE / "source-lock.json"), "result": ref(rp),
        "scoped_kernel_result": v, "source_review": d["source_review"], "limits": d["limits"],
        "author_selected_public_declarations": len(b["author_selected_public_declarations"]),
        "all_explicit_authored_names": names, "actual_authored_kernel_theorems_including_private_and_instance": theorems,
        "literal_endpoint_examples": examples, "additional_independent_examples": d["additional_examples"],
        "private_name_provenance": ref(BASE / "private-name-provenance.json"),
        "author_terminal_and_auditor_controls": ref(BASE / "author-and-control-receipts.json"),
        "integration_examples": ref(BASE / ("integration-" + key + ".lean.txt")),
        "retained_failed_independent_result": ref(oldrun / "result.json"),
        "local_context_diagnostic": ref(BASE / "local-instance-context-diagnostic.json"),
        "freshness": f"All {closure} source-bound project prerequisites rebuilt within the shared fresh100-source private object root before this separate consumer. No previous project objects reused; exact pinned external package objects reused.",
        "kernel_mode": "LeanCert kernel", "axioms": v["observed_axioms"],
        "ten_exact_clean_pins_before_after": True, "original25_byte_exact_against_2b_before_after": True,
        "generated_helpers": "All explicit public/private/local source declarations receive exact kind/kernel/transitive-axiom checks. Generated and anonymous helpers are kernel-compiled and covered transitively, without claiming separate explicit-name checks.",
        "proof_inputs_changed": False, "full_TR04_Target_proved": False, "authoritative_Linux_Comparator": False}
    p = BASE / ("APPROVAL-" + key + ".json")
    p.write_text(json.dumps(a, indent=2) + "\n")
    receipts.append(ref(p))

a = {"passed": True, "reviewer": "/root/recover_verification", "proof_source_authorship": [],
    "recorded_utc": datetime.now(timezone.utc).isoformat(),
    "scope": "Three separately delimited actual execution phase approvals: startup1, header dispatch/metadata2, first-SVD selection6. No full TT execution/approximation/total cost/Target or authoritative CI acceptance.",
    "result": ref(rp), "receipts": receipts,
    "author_terminal_and_auditor_controls": ref(BASE / "author-and-control-receipts.json"),
    "private_name_provenance": ref(BASE / "private-name-provenance.json"),
    "reproducers": [ref(BASE / n) for n in ["prepare.py", "make-replay.py", "replay.py", "source_inventory.py", "check-private-auditor.py", "check-author-results.py", "approve-startup.py", "make-approval.py"]],
    "project_source_count": 100, "successful_commands": 103, "distinct_explicit_named_declarations": 1028,
    "new_authored_source_files": 9, "author_selected_public_names": 97,
    "additional_named_instances_not_in_author_selected_lists": 2,
    "explicit_private_helpers": 62, "all_explicit_authored_names": 161,
    "actual_authored_kernel_theorems_including_private_and_instances": 135,
    "verbatim_endpoint_examples": 70, "additional_independent_examples": 5,
    "retained_failed_batch": {"result": ref(oldrun / "result.json"), "accepted_as_aggregate": False, "startup_scope_independently_passed": True, "first_selection_built_in_this_attempt": False},
    "auditor_negative_custom_axiom_fixture": "Correctly rejected; not accepted as a proof.",
    "project_objects_reused": False, "ten_exact_clean_pins_before_after": True,
    "original25_byte_exact_against_2b_before_after": True,
    "proof_inputs_changed": False, "full_TR04_Target_proved": False, "authoritative_Linux_Comparator": False}
p = BASE / "ACCEPTANCE.json"
p.write_text(json.dumps(a, indent=2) + "\n")
print(json.dumps({"passed": True, "acceptance": ref(p), "result": ref(rp), "receipts": receipts}, indent=2))
