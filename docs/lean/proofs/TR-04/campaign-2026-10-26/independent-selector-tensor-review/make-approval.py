#!/usr/bin/env python3
"""Bind the completed independent replay; never changes mathematical inputs."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[5]


def sha(path):
    assert path.is_file() and not path.is_symlink(), str(path)
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ref(path):
    return {"path": str(path.relative_to(REPO)), "sha256": sha(path)}


run = BASE / "run-attempt-1"
result_path = run / "result.json"
r = json.loads(result_path.read_text())
lock = json.loads((BASE / "source-lock.json").read_text())
assert r["passed"] and r["project_sources"] == 55 and len(r["commands"]) == 57
assert r["driver_sha256"] == sha(BASE / "replay.py")
assert r["source_lock_sha256"] == sha(BASE / "source-lock.json")
assert r["inventory_sha256"] == sha(BASE / "source_inventory.py")
assert r["lean_sha256"] == "1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554"
assert r["project_objects_reused"] is False
assert r["pinned_external_dependency_objects_reused"] is True
assert not r["private_or_local_named_declarations"]
assert all(v["passed"] for k in ["dependencies_before", "dependencies_after", "original25_before", "original25_after"] for v in r[k])
assert all(r["source_unchanged_after"].values())
assert all(r["author_locks_unchanged_after"].values())
for name, digest in r["source_sha256"].items():
    assert sha(run / "sources" / name) == digest
    assert sha(REPO / "lean-statements" / name) == digest
for name, digest in r["consumer_sha256"].items():
    assert sha(run / "sources" / name) == digest
for command in r["commands"]:
    assert command["exit_code"] == 0
    assert sha(run / command["log"]) == command["log_sha256"]

reviews = {
    "selector": {
        "approval": "APPROVED_FROZEN_BEST_CANDIDATE_SELECTOR_COMPONENT_ONLY",
        "expected": (25, 6, 44, 23, 12),
        "source_review": [
            "All six frozen bodies were read. BestCandidateData contains actual addresses and memory, not an error or minimizer oracle. candidateError is the actual squaredErrorSum over those cells.",
            "The fixed 30-label, four-real, thirteen-natural program executes the actual squared-error routine for every candidate. Its first comparison unconditionally accepts candidate zero; arbitrary incoming winning-error real3 is overwritten by the first actual error. Later candidates replace the winner only on strict lessReal, preserving an earlier winner on ties.",
            "The embedded squared-error routine maps labels 0 through 10 to 8 through 18 and its local halt to the actual selector comparison continuation. The caller proof stops before that continuation; ordinary relocation preserves winning real3 and selector registers outside the embedded frame.",
            "Each iteration takes 9*N+15 actual steps. For every legal standalone trace and K>0, the result has winner<K, its actual candidate base, the actual minimum squared error in real3, and exactly unchanged memory. Standalone time is (9*N+15)*K+4; the arbitrary-offset caller returns running at mapped local halt25 after one fewer step, with prefix cost plus the stated quadratic bound and outside-frame registers preserved.",
            "Twelve complete frozen endpoint headers compile verbatim. An additional independent actual-trace example instantiates N=0 and arbitrary incoming error: the returned real3 is zero and some winner<K is selected, with full memory unchanged. Read-only input and candidate arrays may overlap. K=0 has trace existence but no minimum claim."
        ],
        "limits": "Selector component for already stored candidates only. Producing every candidate, invoking this selector from the complete controller, approximation correctness and total global polynomial cost remain separate. No full original Target, authoritative Linux or Comparator acceptance claim.",
        "additional_examples": [{"description": "Every legal standalone trace, K>0, N=0, arbitrary incoming error; actual zero result and preserved memory.", "count": 1}],
        "prop_instance_kind": {"name": "NLA.Proofs.TR04.bestCandidateProgram_nonzero_realRegisters", "expected_actual_kernel_kind": "theorem", "reason": "The named instance proves the Prop NeZero; Lean stores this exact source-bound declaration as thmInfo. The driver keeps strict exact-name theorem expectations."},
    },
    "tensor_operations": {
        "approval": "APPROVED_FROZEN_TENSOR_OPERATIONAL_MEMORY_COMPONENTS_ONLY",
        "expected": (46, 3, 27, 22, 14),
        "source_review": [
            "All three frozen bodies were read. StoresTensor and StoresFrame specify actual memory cells at explicit radix offsets and strided frame addresses. StoresTensor is equivalent to the actual dense readMatrix, and the original Offset representation is transported through the proved original radix bijection.",
            "Tensor merge and unmerge preserve the same physical memory and base. The exact identity (j+n*i)*prod(rest)+offset = i*(n*prod(rest))+j*prod(rest)+offset proves that no copy or runtime permutation is needed.",
            "Contraction uses Q transpose and lifting uses Q through the literal strided matrix-multiply data. A full U prefix retains physical row stride m; a dense gathered Q has row stride q. These generic algebraic operations do not require orthogonality.",
            "The safety premises are q<=stride and actual frame/output and input/output block disjointness. Input and frame may overlap one another because both are read-only. Every legal caller trace at every offset returns running at mapped local halt21 with the actual output tensor, unchanged input and frame, unchanged memory outside output, outside-frame registers preserved, and prefix cost plus the actual cubic matrix-multiply bound. Empty dimensions are included.",
            "Fourteen complete frozen endpoint headers compile verbatim. Two independently composed actual-caller examples prove full-U-prefix contraction with physical stride m and dense-Q lifting with physical stride q directly from literal readMatrix input equations. They project the actual output StoresTensor from the complete all-trace operational theorem, not an evaluator premise."
        ],
        "limits": "Operational contraction/lift and memory-format components only. Complete approximation program control, global workspace ownership and total global cost remain separate. No full original Target, authoritative Linux or Comparator acceptance claim.",
        "additional_examples": [{"description": "Full-U prefix contraction with actual row stride m.", "count": 1}, {"description": "Dense-Q lifting with actual row stride q.", "count": 1}],
    },
}

receipts = []
for b in lock["blocks"]:
    key = b["key"]
    review = reviews[key]
    block = r["blocks"][key]
    closure, owned, names, theorems, literals = review["expected"]
    assert block["passed"] and block["all_named_declaration_checks_passed"]
    assert block["project_closure_count"] == closure and block["owned_source_count"] == owned
    assert len(block["owned_declarations"]) == names
    assert block["actual_owned_kernel_theorem_count"] == theorems
    assert block["literal_examples"] == literals
    assert block["observed_axioms"] == ["Classical.choice", "Quot.sound", "propext"]
    assert sha(REPO / b["author_lock_path"]) == b["author_lock_sha256"]
    for v in b["records"]:
        assert sha(REPO / v["path"]) == v["sha256"]
    approval = {
        "passed": True,
        "approval": review["approval"],
        "reviewer": "/root/recover_verification",
        "proof_source_authorship": [],
        "review_recorded_utc": datetime.now(timezone.utc).isoformat(),
        "execution_started_utc": r["started_utc"],
        "execution_finished_utc": r["finished_utc"],
        "author": b["author"],
        "author_source_lock": {"path": b["author_lock_path"], "sha256": b["author_lock_sha256"]},
        "independent_source_lock": ref(BASE / "source-lock.json"),
        "result": ref(result_path),
        "scoped_kernel_result": block,
        "source_review": review["source_review"],
        "limits": review["limits"],
        "freshness": f"All {closure} source-bound project prerequisites rebuilt in the shared fresh 55-source audit into an empty private object root. No prior project objects reused; only exact pinned external package objects reused. The separate consumer imports only its own frozen scope.",
        "kernel_mode": "LeanCert kernel",
        "axioms": block["observed_axioms"],
        "authored_source_files": owned,
        "authored_named_declarations": names,
        "authored_actual_kernel_theorems": theorems,
        "authored_theorem_keywords": block["owned_theorem_kinds"],
        "literal_endpoint_examples": literals,
        "additional_examples": review["additional_examples"],
        "integration_examples": ref(BASE / ("integration-" + key + ".lean.txt")),
        "consumer": {"path": str((run / "sources" / r["consumer_bindings"][key]["source"]).relative_to(REPO)), "sha256": r["consumer_sha256"][r["consumer_bindings"][key]["source"]]},
        "ten_exact_clean_pins_before_after": True,
        "original25_byte_exact_against_2b_before_after": True,
        "private_or_local_explicit_declarations": [],
        "generated_declaration_scope": "Explicitly named source declarations receive kind/kernel/axiom checks. Generated and anonymous helpers are checked by compilation and transitive axiom auditing, not claimed as separate explicit-name assertions.",
        "proof_inputs_changed": False,
        "full_TR04_Target_proved": False,
        "authoritative_Linux_Comparator": False,
    }
    if "prop_instance_kind" in review:
        approval["prop_instance_kind"] = review["prop_instance_kind"]
    path = BASE / ("APPROVAL-" + key + ".json")
    path.write_text(json.dumps(approval, indent=2) + "\n")
    receipts.append(ref(path))

acceptance = {
    "passed": True,
    "reviewer": "/root/recover_verification",
    "proof_source_authorship": [],
    "scope": "Two independent support-only source reviews and fresh kernel consumers: frozen selector6 and tensor operational3.",
    "recorded_utc": datetime.now(timezone.utc).isoformat(),
    "result": ref(result_path),
    "receipts": receipts,
    "reproducers": [ref(BASE / name) for name in ["prepare.py", "replay.py", "source_inventory.py", "make-approval.py"]],
    "project_source_count": 55,
    "successful_commands": 57,
    "distinct_explicit_named_declarations": len(r["declarations"]),
    "new_authored_source_files": 9,
    "new_authored_named_declarations": 71,
    "new_authored_actual_kernel_theorems": 45,
    "verbatim_endpoint_examples": 26,
    "additional_actual_trace_examples": 3,
    "project_objects_reused": False,
    "ten_exact_clean_pins_before_after": True,
    "original25_byte_exact_against_2b_before_after": True,
    "axioms": ["Classical.choice", "Quot.sound", "propext"],
    "retained_failed_Lean_attempts_in_this_audit": [],
    "proof_inputs_changed": False,
    "full_TR04_Target_proved": False,
    "authoritative_Linux_Comparator": False,
}
path = BASE / "ACCEPTANCE.json"
path.write_text(json.dumps(acceptance, indent=2) + "\n")
print(json.dumps({"passed": True, "acceptance": ref(path), "result": ref(result_path), "receipts": receipts}, indent=2))
