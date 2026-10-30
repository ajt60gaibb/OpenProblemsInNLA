#!/usr/bin/env python3
"""Validate and bind the completed support-only independent audit."""
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
auxp = BASE / "auxiliary-input-check.json"
aux = json.loads(auxp.read_text())
assert r["passed"] and r["project_sources"] == 40 and len(r["commands"]) == 42
assert r["driver_sha256"] == sha(BASE / "replay.py")
assert r["inventory_sha256"] == sha(BASE / "source_inventory.py")
assert r["source_lock_sha256"] == sha(BASE / "source-lock.json")
assert r["lean_sha256"] == "1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554"
assert r["project_objects_reused"] is False and r["pinned_external_dependency_objects_reused"] is True
assert all(v["passed"] for k in ["dependencies_before", "dependencies_after", "original25_before", "original25_after"] for v in r[k])
assert all(r["source_unchanged_after"].values()) and all(r["author_locks_unchanged_after"].values())
assert not r["private_or_local_named_declarations"]
failed_run = BASE / "run-attempt-1"
failed = json.loads((failed_run / "result.json").read_text())
assert failed["passed"] is False
assert [(c["source"], c["exit_code"]) for c in failed["commands"] if c["exit_code"]] == [("Independent_assembly_Consumer.lean", 1)]
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
assert aux["passed"] and aux["generator_check"]["exit_code"] == 0
assert sha(BASE / "generator-check.log") == aux["generator_check"]["log_sha256"]
for v in aux["support_inputs"] + aux["author_results"] + [aux["retained_layout_superseded_lock"], aux["retained_layout_initial_diagnostic"]]:
    assert sha(REPO / v["path"]) == v["sha256"]

details = {
    "layout": {
        "expected": (9, 4, 88, 65, 19, 2),
        "approval": "APPROVED_FROZEN_TT_MEMORY_ALLOCATION_COMPONENT_ONLY",
        "source_review": [
            "All four frozen source bodies were read. The allocation starts at the exact original input base 2*d-1 and reserves input N, three N^2 SVD squares, two N sigma arrays, d N^2 frames, four metadata cells per level, two N-cell dense work buffers, and K N-cell candidates. Its exclusive endpoint is B+(d+3)*N^2+(K+5)*N+4*d.",
            "The exact original Shape/Size bound is endAddress<=20*(Size+1)^3 under the explicit K<=N+1 premise. Frame and metadata indices retain level<order and field<4; distinct metadata fields/levels are injective and distinct candidates and frames are disjoint. Empty blocks use the literal model's disjointness convention.",
            "First and child SVD output disjointness uses separate m<=N and l<=N bounds. Actual writeSVD protection is proved for the input prefix, later regions, work/candidate addresses, and every other level's frame, with all necessary dimension/level hypotheses retained.",
            "Frames fit N^2 from individual dimension bounds. An N-cell work buffer requires its separate rectangular product bound; the matrix safety theorems preserve these hinput/houtput assumptions. Contraction/lifting records have the actual strided readMatrix and transpose meanings, with output in workB and input in workA.",
            "Nineteen full endpoint headers compile verbatim. Two additional tests expand the original heap expression into Size and instantiate actual first-SVD disjointness at zero-by-zero dimensions."
        ],
        "limits": "Allocation/address/read-protection and actual matrix-entry safety only. The K<=N+1, recursive rectangular work-size and level invariants must be supplied by later program proofs. No full program execution, approximation, total charged complexity, Target, Linux or Comparator acceptance claim.",
        "retained_diagnostic": {"superseded_lock": aux["retained_layout_superseded_lock"], "initial_failed_build_log": aux["retained_layout_initial_diagnostic"], "explanation": "The earlier cleanup attempt left an unconstrained address in contraction_inputsOutsideOutput and failed with sorryAx in that unaccepted output. The final e6b0ca48 lock supplies the explicit address and is the sole accepted source scope. Both historical files remain unchanged and unaccepted."},
    },
    "assembly": {
        "expected": (36, 4, 65, 18, 18, 11),
        "approval": "APPROVED_FROZEN_FINITE_TT_ASSEMBLY_AND_HEADER_PREFIX_ONLY",
        "source_review": [
            "All four frozen source bodies and the complete retained generator were read. installCodeBank copies every non-halt ordinary or SVD instruction with literal label/register/constant relocation; only local halt cells and addresses outside the bank keep the caller instruction. The exact code fields construct genuine RoutineEmbedding objects and preserve earlier embeddings when later bank intervals are disjoint.",
            "The fixed ttProgram has 512 labels, 16 real registers, 128 natural registers and an empty constant pool. Six consecutive banks cover header 0..10, matrix 11..32, copy 33..39, gather 40..65, threshold 66..88 and selector 89..118. Their literal continuations at 10/32/39/65/88/114 are preserved. Static caller code at all labels>=119 is exactly unchanged by bank installation; it contains 276 generated instructions, ending at label394.",
            "The source proves by kernel-checked finite decision that the only SVD opcodes among all 512 labels are first167 and child237. The generic actual trace SVD theorem preserves every legal complete rectangular tuple, exact memory write and actual cubic charge under the literal OutputBlocksDisjoint precondition. Two independent concrete-site consumers instantiate these complete conclusions at the distinct actual register maps and next labels168/238.",
            "Actual Start enters the header bank without supplying decoded header values or their product. Every legal trace computes original DenseSize in natural2, returns running at label10, retains the entire InputMemory store, and costs at most7*Size. Outside-frame natural registers retain their initial zero; an additional consumer checks actual controller tag97 and zero127 explicitly.",
            "Eighteen complete theorem headers compile verbatim, including all six continuation equations, generic bank exits/outside cells, both scalar/SVD trace interfaces, complete SVD-site classification, initial relation and header prefix. Eleven further checks cover fixed cardinalities, six genuine embeddings into the complete program, corrected literal prefix tied=1, outside header registers, and both complete actual SVD replies.",
            "Read-only generate-controller.py --check reproduces exact frozen program and controller-layout.json bytes. The independently found prefix fallback tied=0 contract mismatch was corrected to tied=1 before this lock; the finding and correction remain retained and hash-bound. This support review accepts the corrected finite syntax and proved prefixes, not the still unproved later execution phases."
        ],
        "limits": "Finite syntax, generic code-bank construction, exact embeddings, actual initial header prefix and conditional actual SVD-step interfaces only. No claim that both SVD sites are reached, that every later routine entry satisfies its hypotheses, that every candidate is produced, or that the complete program returns the required approximation with total polynomial cost. Full original Target, authoritative Linux and Comparator acceptance remain open.",
        "generator_and_prefix_finding": aux["support_inputs"],
    },
}

receipts = []
for b in lock["blocks"]:
    key = b["key"]
    d = details[key]
    v = r["blocks"][key]
    closure, files, names, theorems, literals, extras = d["expected"]
    assert v["passed"] and v["all_named_declaration_checks_passed"]
    assert v["project_closure_count"] == closure and v["owned_source_count"] == files
    assert len(v["owned_declarations"]) == names and v["actual_owned_kernel_theorem_count"] == theorems
    assert v["literal_examples"] == literals
    assert v["observed_axioms"] == ["Classical.choice", "Quot.sound", "propext"]
    assert sha(REPO / b["author_lock_path"]) == b["author_lock_sha256"]
    a = {
        "passed": True, "approval": d["approval"], "reviewer": "/root/recover_verification",
        "proof_source_authorship": [], "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "execution_started_utc": r["started_utc"], "execution_finished_utc": r["finished_utc"],
        "author": b["author"],
        "author_source_lock": {"path": b["author_lock_path"], "sha256": b["author_lock_sha256"]},
        "independent_source_lock": ref(BASE / "source-lock.json"), "result": ref(rp),
        "auxiliary_input_check": ref(auxp), "scoped_kernel_result": v,
        "retained_independent_consumer_diagnostic": ref(BASE / "consumer-syntax-diagnostic.json"),
        "retained_failed_independent_result": ref(failed_run / "result.json"),
        "source_review": d["source_review"], "limits": d["limits"],
        "authored_source_files": files, "authored_named_declarations": names,
        "authored_actual_kernel_theorems": theorems, "literal_endpoint_examples": literals,
        "additional_independent_examples": extras,
        "integration_examples": ref(BASE / ("integration-" + key + ".lean.txt")),
        "freshness": f"All {closure} project prerequisites rebuilt inside the shared fresh40-source private object root. No prior project objects reused; exact pinned external package objects reused. A separate consumer imports only this scope.",
        "kernel_mode": "LeanCert kernel", "axioms": v["observed_axioms"],
        "ten_exact_clean_pins_before_after": True, "original25_byte_exact_against_2b_before_after": True,
        "private_or_local_explicit_declarations": [],
        "generated_declaration_scope": "Explicitly named source declarations receive exact kind/kernel/axiom checks. Compilation and transitive axiom auditing cover generated or anonymous helpers; no separate explicit-name check is claimed for them.",
        "proof_inputs_changed": False, "full_TR04_Target_proved": False,
        "authoritative_Linux_Comparator": False,
    }
    for name in ["retained_diagnostic", "generator_and_prefix_finding"]:
        if name in d: a[name] = d[name]
    p = BASE / ("APPROVAL-" + key + ".json")
    p.write_text(json.dumps(a, indent=2) + "\n")
    receipts.append(ref(p))

a = {
    "passed": True, "reviewer": "/root/recover_verification", "proof_source_authorship": [],
    "recorded_utc": datetime.now(timezone.utc).isoformat(),
    "scope": "Two supporting scopes: concrete TT memory layout4 and finite assembly4. No complete program correctness or Target acceptance.",
    "result": ref(rp), "receipts": receipts, "auxiliary_input_check": ref(auxp),
    "reproducers": [ref(BASE / n) for n in ["prepare.py", "replay.py", "source_inventory.py", "check-auxiliary.py", "make-approval.py"]],
    "project_source_count": 40, "successful_commands": 42,
    "distinct_explicit_named_declarations": len(r["declarations"]),
    "new_authored_sources": 8, "new_authored_named_declarations": 153,
    "new_authored_actual_kernel_theorems": 83,
    "verbatim_endpoint_examples": 37, "additional_independent_examples": 13,
    "project_objects_reused": False, "ten_exact_clean_pins_before_after": True,
    "original25_byte_exact_against_2b_before_after": True,
    "axioms": ["Classical.choice", "Quot.sound", "propext"],
    "retained_failed_Lean_attempts_in_this_independent_audit": [{"result": ref(failed_run / "result.json"), "diagnostic": ref(BASE / "consumer-syntax-diagnostic.json"), "initial_consumer_integration": ref(BASE / "integration-assembly-attempt-1.lean.txt"), "accepted": False}],
    "proof_inputs_changed": False, "full_TR04_Target_proved": False, "authoritative_Linux_Comparator": False,
}
p = BASE / "ACCEPTANCE.json"
p.write_text(json.dumps(a, indent=2) + "\n")
print(json.dumps({"passed": True, "acceptance": ref(p), "result": ref(rp), "receipts": receipts}, indent=2))
