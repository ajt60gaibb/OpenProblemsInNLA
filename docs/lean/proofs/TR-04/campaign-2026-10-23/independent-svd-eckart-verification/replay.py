#!/usr/bin/env python3
"""Fresh independent kernel audit of exactly eleven frozen TR04 SVD support sources.

Never edits proof/canonical inputs and never claims a TR04 Target proof.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import tempfile
from source_inventory import without_comments, declarations_of

BASE = Path(__file__).resolve().parent
REPO = Path(__file__).resolve().parents[6]
PROJECT = REPO / "lean-statements"
LEAN = REPO.parent / "tooling/lean-4.33.1-darwin_aarch64/bin/lean"
PACKAGES = (PROJECT / ".lake/packages").resolve()
EVIDENCE = BASE / "run"
PROOF_BASE = "2b049df5e9b15318987f3fa592b1a7c65a0c0057"
LOCK = BASE / "frozen-svd-source-lock.json"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(argv, **kwargs):
    p = subprocess.run(list(map(str, argv)), text=True, capture_output=True, **kwargs)
    return {"argv": list(map(str, argv)), "exit_code": p.returncode, "stdout": p.stdout, "stderr": p.stderr}


def dependencies():
    records = []
    for item in json.loads((PROJECT / "lake-manifest.json").read_text())["packages"]:
        directory = PACKAGES / item["name"]
        head = run(["git", "-C", directory, "rev-parse", "HEAD"])
        status = run(["git", "-C", directory, "status", "--porcelain", "--untracked-files=no"])
        records.append({"name": item["name"], "expected_revision": item["rev"],
                        "directory": str(directory), "head": head, "status": status,
                        "passed": head["exit_code"] == status["exit_code"] == 0
                        and head["stdout"].strip() == item["rev"] and not status["stdout"].strip()})
    if len(records) != 10 or not all(r["passed"] for r in records):
        raise RuntimeError("Exact ten dependency pins/cleanliness failed")
    return records


expected = json.loads(LOCK.read_text())["records"]
assert len(expected) == 11 and all(sha((REPO / r["path"]).read_bytes()) == r["sha256"] for r in expected)
modules = [r["path"].removeprefix("lean-statements/").removesuffix(".lean").replace("/", ".") for r in expected]
roots = modules
frozen, visiting = {}, set()


def freeze(module):
    name = module.replace(".", "/") + ".lean"
    if name in frozen:
        return
    if name in visiting:
        raise RuntimeError("Local import cycle: " + module)
    visiting.add(name)
    data = (PROJECT / name).read_bytes()
    clean = without_comments(data.decode())
    for line in clean.splitlines():
        m = re.fullmatch(r"import\s+([A-Za-z0-9_.]+)\s*", line)
        if m and (PROJECT / (m[1].replace(".", "/") + ".lean")).is_file():
            freeze(m[1])
    lexical = re.sub(r'"(?:\\.|[^"\\])*"', '""', clean)
    if re.search(r"\b(sorry|admit|axiom|implemented_by|unsafe)\b|trustCompiler|debug\.skipKernelTC", lexical):
        raise RuntimeError("Unexpected proof-trust construct in frozen source: " + name)
    frozen[name] = data
    visiting.remove(name)


for module in roots:
    freeze(module)
assert {n for n in frozen if n.startswith("NLA/Proofs/TR04/")} == {
    r["path"].removeprefix("lean-statements/") for r in expected}
assert len(frozen) == 12
declarations = [d for name, data in frozen.items() for d in declarations_of(name, data)]
assert all(d["visibility"] == "public" for d in declarations)
assert all(d["kind"] in {"theorem", "lemma", "def", "abbrev", "inductive", "structure"} for d in declarations)
audit = "\n".join("import " + m for m in roots) + '''
set_option autoImplicit false
set_option leancert.trust "kernel"
open Lean Elab Command in
elab "#assert_kind " n:ident expected:str : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let some info := (← getEnv).find? decl | throwErrorAt n "missing actual constant"
  match expected.getString, info with
  | "theorem", .thmInfo _ => pure ()
  | "definition", .defnInfo _ => pure ()
  | "inductive", .inductInfo _ => pure ()
  | _, _ => throwErrorAt n "constant kind differs from frozen source"
  logInfo m!"AUDITED_KIND {decl} {expected.getString}"
'''
for d in declarations:
    kind = "theorem" if d["kind"] in {"theorem", "lemma"} else "inductive" if d["kind"] in {"inductive", "structure"} else "definition"
    audit += f'#assert_kind {d["name"]} "{kind}"\n#assert_trust kernel {d["name"]}\n#print axioms {d["name"]}\n'
audit += '\nnoncomputable section\nopen NLA.Computation.SVDMachine NLA.Proofs.TR04.SVD\nexample (m l : ℕ) (B : Matrix (Fin m) (Fin l) ℝ) :\n    ∃ U sigma V, ValidSVD B U sigma V := exists_validSVD B\nexample (l : ℕ) (B : Matrix (Fin 0) (Fin l) ℝ) :\n    ∃ U sigma V, ValidSVD B U sigma V := exists_validSVD B\nexample (m : ℕ) (B : Matrix (Fin m) (Fin 0) ℝ) :\n    ∃ U sigma V, ValidSVD B U sigma V := exists_validSVD B\nsection\nvariable {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}\n    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}\n    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)\nexample (r : ℕ) (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ r) :\n    tailEnergy sigma r ≤ matrixEnergy (B - Y) := validSVD_eckartYoung h r Y hY\nexample (r : ℕ) : matrixEnergy (B - truncate U sigma V r) = tailEnergy sigma r :=\n  validSVD_truncate_error h r\nexample (r : ℕ) : Matrix.rank (truncate U sigma V r) ≤ r ∧\n    ∀ Y, Matrix.rank Y ≤ r → matrixEnergy (B - truncate U sigma V r) ≤ matrixEnergy (B - Y) :=\n  validSVD_truncate_best h r\nexample (r : ℕ) : Matrix.rank B ≤ r ↔ tailEnergy sigma r = 0 :=\n  validSVD_rank_le_iff_tail_zero h r\nexample (a : Fin (min m l)) (ha : 0 < sigma a)\n    (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ a.val + 1)\n    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1)) :\n    Y = projectMatrix (columnSpace Y) B ∧ Matrix.rank Y = a.val + 1 ∧\n      (∀ k, sigma a < sigma k → (columnSpace Y).starProjection\n        (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) =\n          matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) ∧\n      (∀ k, sigma k < sigma a → (columnSpace Y).starProjection\n        (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) = 0) :=\n  validSVD_eckartYoung_eq_last_retained h a ha Y hY heq\nexample (r : ℕ) (hr : r ≤ min m l) (tau : ℝ) (htau : 0 < tau)\n    (habove : ∀ k, k.val < r → tau ≤ sigma k)\n    (hbelow : ∀ k, r ≤ k.val → sigma k ≤ tau)\n    (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ r)\n    (heq : matrixEnergy (B - Y) = tailEnergy sigma r) :\n    Y = projectMatrix (columnSpace Y) B ∧ Matrix.rank Y = r ∧\n      (∀ k, tau < sigma k → (columnSpace Y).starProjection\n        (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) =\n          matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) ∧\n      (∀ k, sigma k < tau → (columnSpace Y).starProjection\n        (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) = 0) :=\n  validSVD_eckartYoung_eq_threshold h r hr tau htau habove hbelow Y hY heq\nend\nend\n'
frozen["IndependentSVDConsumer.lean"] = audit.encode()
preserved = json.loads((BASE.parent / "geometry-input-preservation-result.json").read_text())["locked_original_model_review_inputs"]
assert len(preserved) == 25


def originals():
    records = []
    for item in preserved:
        path = item["path"]
        data = (REPO / path).read_bytes()
        original = subprocess.check_output(["git", "show", f"{PROOF_BASE}:{path}"], cwd=REPO)
        records.append({"path": path, "sha256": sha(data), "passed": data == original})
    if not all(r["passed"] for r in records):
        raise RuntimeError("An original input changed")
    return records


EVIDENCE.mkdir(exist_ok=False)
for name, data in frozen.items():
    p = EVIDENCE / "sources" / name
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(data)
result = {"scope": "Independent fresh local kernel audit of exactly eleven frozen TR04 SVD support modules; no Target proof, solver, approximation guarantee, termination or polynomial complexity claim",
          "reviewer": "/root/recover_verification", "self_authored_proof_sources": [],
          "frozen_support_modules": 11, "actual_local_sources": 12, "exact_type_examples": 9,
          "source_lock_sha256": sha(LOCK.read_bytes()), "driver_sha256": sha(Path(__file__).read_bytes()),
          "source_sha256": {n: sha(d) for n, d in frozen.items()}, "declarations": declarations,
          "support_declarations": [d for d in declarations if d["source"].startswith("NLA/Proofs/TR04/")],
          "lean_version": run([LEAN, "--version"]), "lean_sha256": sha(LEAN.read_bytes()),
          "dependencies_before": dependencies(), "original25_before": originals(),
          "project_objects_reused": False, "pinned_external_dependency_objects_reused": True,
          "commands": [], "full_TR04_Target_proved": False, "authoritative_Linux_Comparator": False}
try:
    with tempfile.TemporaryDirectory(prefix="objects-", dir=BASE) as temporary:
        fresh = Path(temporary)
        source, output = fresh / "source", fresh / "output"
        output.mkdir()
        for name, data in frozen.items():
            p = source / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(data)
        libraries = [p / ".lake/build/lib/lean" for p in sorted(PACKAGES.iterdir()) if (p / ".lake/build/lib/lean").is_dir()]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [output, *libraries, LEAN.parent.parent / "lib/lean"])))
        result["LEAN_PATH"] = env["LEAN_PATH"]
        for name in frozen:
            target = output / Path(name).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            command = run([LEAN, "-R", source, "-o", target, source / name], cwd=source, env=env, timeout=180)
            command["source"] = name
            result["commands"].append(command)
            (EVIDENCE / (name.replace("/", "-") + ".log")).write_text(command["stdout"] + command["stderr"])
            print(name + ": " + str(command["exit_code"]), flush=True)
            if command["exit_code"]:
                break
except Exception as error:
    result["exception"] = repr(error)
result["dependencies_after"] = dependencies()
result["original25_after"] = originals()
result["source_unchanged_after"] = {n: (PROJECT / n).read_bytes() == d for n, d in frozen.items() if n != "IndependentSVDConsumer.lean"}
if len(result["commands"]) == len(frozen) and result["commands"][-1]["exit_code"] == 0:
    log = result["commands"][-1]["stdout"] + result["commands"][-1]["stderr"]
    kinds = re.findall(r"AUDITED_KIND (\S+) (\S+)", log)
    result["kind_check_count"] = len(kinds)
    axiom_records = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", log)
    result["observed_axioms"] = sorted({a.strip() for _, body in axiom_records for a in body.split(",") if a.strip()})
    result["axiom_report_count"] = len(axiom_records) + len(no_axioms)
    result["all_declaration_names_reported"] = sorted(n for n, _ in axiom_records) + sorted(no_axioms)
    result["all_named_declaration_checks_passed"] = len(kinds) == len(declarations) and len(axiom_records) + len(no_axioms) == len(declarations)
result["passed"] = (len(result["commands"]) == len(frozen) and all(c["exit_code"] == 0 for c in result["commands"])
                    and all(result["source_unchanged_after"].values()) and result.get("all_named_declaration_checks_passed", False)
                    and set(result.get("observed_axioms", [])) <= ALLOWED and "exception" not in result)
(EVIDENCE / "result.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": result["passed"], "commands": len(result["commands"]), "declarations": len(declarations),
                  "support_declarations": len(result["support_declarations"]), "axioms": result.get("observed_axioms"),
                  "exception": result.get("exception")}, indent=2))
raise SystemExit(0 if result["passed"] else 1)
