#!/usr/bin/env python3
"""Identify the actual endpoint imports from the immutable freshly compiled record."""
import hashlib,json
from pathlib import Path
p=Path(__file__).resolve().parent;r=json.loads((p/"result.json").read_bytes());assert r["passed"]
records={e["module"]:e for e in r["source_records"]};seen=set();external=set()
def visit(n):
    if n in seen:return
    if n not in records:external.add(n);return
    seen.add(n)
    for child in records[n]["imports"]:visit(child)
visit("NLA.Proofs.TR26.IsotropicDegree")
proofs=sorted(n for n in seen if n.startswith("NLA.Proofs.TR26."))
ck=next(c for c in r["checks"] if c["check"]=="all_declaration_kinds_kernel_and_standard_axioms")
axioms=ck["closures"]["NLA.Proofs.TR26.isotropic_degree"]
passed=len(seen)==34 and len(proofs)==32 and set(axioms)=={"propext","Classical.choice","Quot.sound"} and all(e == "Lean" or e.startswith(("Mathlib","LeanCert")) for e in external)
out={"scope":"Exact endpoint import closure; the full source replay additionally compiles the unused CurveNormalRank module and Reviewed boundary","checkpoint_commit":r["checkpoint_commit"],"passed":passed,"own_modules":len(seen),"proof_modules":len(proofs),"records":[records[n] for n in sorted(seen)],"external_pinned_imports":sorted(external),"isotropic_endpoint_axioms":axioms,"fresh_replay_result_sha256":hashlib.sha256((p/"result.json").read_bytes()).hexdigest(),"script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(p/"ENDPOINT_IMPORT_CLOSURE.json").write_text(json.dumps(out,indent=2)+"\n");print(json.dumps({"passed":passed,"own_modules":len(seen),"proof_modules":len(proofs),"axioms":axioms}));raise SystemExit(0 if passed else 1)

