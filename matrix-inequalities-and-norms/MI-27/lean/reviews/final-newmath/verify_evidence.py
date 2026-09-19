#!/usr/bin/env python3
"""Read-only authentication of MI27 retained evidence; never invokes Lean."""
from pathlib import Path
import gzip, hashlib, json, re

ROOT = Path(__file__).resolve().parents[3]
D = ROOT / ".local-recovery-20260918"
S = D / "final-review-packets/MI27-v1"
E = D / "verification/MI27-local-20260919"
T = D / "verification/MI27-type-preflight-118"
OUT = Path(__file__).resolve().parent
sha = lambda b: hashlib.sha256(b).hexdigest()
read = lambda p: json.loads(p.read_text())
snapshot_bytes = (S / "REVIEW-SNAPSHOT.json").read_bytes()
assert sha(snapshot_bytes) == "d9a8bb1b4cf6e228d6c211c57f58cfd79e710f3961dffe65cb06db6c39249790"
snap = json.loads(snapshot_bytes)
for rel, expected in snap["files"].items():
    assert sha((S / rel).read_bytes()) == expected, rel
assert {str(p.relative_to(S)) for p in S.rglob("*") if p.is_file()} == set(snap["files"]) | {"REVIEW-SNAPSHOT.json"}
cfg = read(S / "comparator.json")
freeze = read(S / "STATEMENT-FREEZE.json")
assert len(cfg["theorem_names"]) == len(set(cfg["theorem_names"])) == 20
assert cfg["theorem_names"] == freeze["contract_names"]
assert cfg["definition_names"] == []
assert set(cfg["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
for rel, expected in freeze["frozen_files"].items():
    assert sha((S / rel).read_bytes()) == expected, rel

def without_comments(text):
    """Remove nested Lean comments, preserving newline positions."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1; i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1; i += 2
        elif depth:
            if text[i] == "\n": out.append("\n")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i]); i += 1
    assert depth == 0
    return "".join(out)

sources = {p[:-5].replace("/", "."): p for p in snap["files"]
           if p.endswith(".lean") and (p.startswith("NLA/") or p == "Solution.lean")}
imports = {}
for mod, rel in sources.items():
    text = without_comments((S / rel).read_text())
    assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b", text), rel
    ds = [v for line in text.splitlines() if line.startswith("import ")
          for v in line[7:].split()]
    assert "Challenge" not in ds
    imports[mod] = [v for v in ds if v.startswith("NLA.") or v == "Solution"]
    assert all(v in sources for v in imports[mod]), (mod, imports[mod])
closures = {}
def closure(mod):
    if mod not in closures:
        closures[mod] = {mod}
        for dep in imports[mod]:
            closures[mod] |= closure(dep)
    return closures[mod]
assert closure("Solution") == set(sources)
assert len(sources) == 52
prep = read(D / "reviews/MI27-final-newmath-prep/PREPARATORY-READSET.json")
for old, expected in prep["source_hashes"].items():
    rel = str(Path(old).relative_to(".local-recovery-20260918/local-lean"))
    assert sha((S / rel).read_bytes()) == expected, rel
for mod, rel in sources.items():
    assert (D / "local-lean" / rel).read_bytes() == (S / rel).read_bytes(), rel

audit_bytes = (E / "LOCAL-REPLAY-AUDIT.json").read_bytes()
assert sha(audit_bytes) == "17230c39a125c0f67931aa3259679ff7fa6e14b90541c353fe99cb3dd938a390"
audit = json.loads(audit_bytes)
receipts, receipt_hashes = {}, {}
for name, item in audit["lossless_original_receipts"].items():
    data = (E / item["file"]).read_bytes()
    assert sha(data) == item["gzip_sha256"], name
    raw = gzip.decompress(data)
    assert sha(raw) == item["original_sha256"], name
    live = D / "local-lean/runs" / name / "RECEIPT.json"
    assert live.read_bytes() == raw, name
    receipts[name] = json.loads(raw)
    receipt_hashes[name] = sha(raw)
assert receipt_hashes["recovery-118"] == audit["aggregate_receipt_sha256"]
last = receipts["recovery-118"]
assert last["completed_modules"] == 55 and not last["failed_modules"] and not last["blocked_modules"]
cmds = {name: {c["module"]: c for c in r["commands"]} for name, r in receipts.items()}
current_outputs = {mod: cmds["recovery-118"][mod]["output_sha256"] for mod in sources}
records = []
for mod, rel in sorted(sources.items()):
    expected = snap["files"][rel]
    name, seen, steps = "recovery-118", set(), 0
    while True:
        assert name not in seen, (mod, "reuse cycle")
        seen.add(name)
        r, c = receipts[name], cmds[name][mod]
        assert r["compiler_sha256"] == audit["compiler_sha256"]
        assert c["source_sha256"] == expected, (mod, name)
        assert c["output_sha256"] == current_outputs[mod], (mod, name)
        for dep in closure(mod):
            value = r["source_inputs"][sources[dep]]
            if isinstance(value, dict): value = value["sha256"]
            assert value == snap["files"][sources[dep]], (mod, name, dep)
        if c.get("status") == "reused_exact_successful_local_output":
            assert c["transitive_source_hashes"] == {sources[d]: snap["files"][sources[d]] for d in closure(mod)}
            prior = Path(c["prior_receipt"]).parent.name
            assert receipt_hashes[prior] == c["prior_receipt_sha256"], (mod, name)
            name, steps = prior, steps + 1
            continue
        assert c["exit_code"] == 0, (mod, name)
        assert c["argv"][1:3] == ["--threads=1", "--memory=4096"]
        assert c["argv"][-1] == rel
        assert c["dependency_olean_sha256"] == {dep: current_outputs[dep] for dep in imports[mod]}, (mod, name)
        log = E / "logs" / name / (mod + ".log")
        assert sha(log.read_bytes()) == c["log_sha256"], (mod, name)
        assert not re.search(r"(^|\n).*\berror:", log.read_text()), (mod, name)
        output = D / "local-lean/.lake/build/lib/lean" / (rel[:-5] + ".olean")
        assert sha(output.read_bytes()) == current_outputs[mod], mod
        records.append({"module": mod, "fresh_run": name, "reuse_steps": steps,
                        "source_sha256": expected, "log_sha256": c["log_sha256"],
                        "output_sha256": current_outputs[mod]})
        break
env = read(E / "LOCAL-ENVIRONMENT.json")
assert sha(Path(env["compiler"]).read_bytes()) == audit["compiler_sha256"]
assert sha((E / "serial_compile_recovery.py").read_bytes()) == audit["runner_sha256"]
actual_log = (E / "logs/recovery-118/Solution.log").read_text()
axioms = {name: [v.strip() for v in xs.split(",")] for name, xs in
          re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", actual_log)}
assert list(axioms) == cfg["theorem_names"]
assert all(set(xs) <= set(cfg["permitted_axioms"]) for xs in axioms.values())
assert axioms == read(E / "actual-axioms.json")
assert (S / "Solution.lean").read_text().count("#assert_trust kernel ") == 20
type_audit = read(T / "AUDIT.json")
assert sha((T / "AUDIT.json").read_bytes()) == "8ebb6afdb40ed9c83abad156d5e6fd522bddfcb000da71181afd34af1cc620db"
assert type_audit["receipt_sha256"] == receipt_hashes["recovery-118"]
typelogs = [(T / (m + ".log")).read_bytes() for m in ("MI27ChallengeTypes118", "MI27SolutionTypes118")]
assert typelogs[0] == typelogs[1]
assert sha(typelogs[0]) == type_audit["log_sha256"]
for marker in ("TYPEJSON", "LEVELJSON"):
    names = re.findall(marker + r" (NLA\.MI27\.\w+) ", typelogs[0].decode())
    assert names == cfg["theorem_names"], marker
for mod in ("MI27ChallengeTypes118", "MI27SolutionTypes118"):
    c = cmds["recovery-118"][mod]
    assert c["exit_code"] == 0
    assert c["source_sha256"] == sha((T / (mod + ".lean")).read_bytes())
    assert c["log_sha256"] == sha((T / (mod + ".log")).read_bytes())
    assert c["argv"][-1] == mod + ".lean"
    assert c["dependency_olean_sha256"] == {dep: cmds["recovery-118"][dep]["output_sha256"]
                                            for dep in (["Challenge"] if "Challenge" in mod else ["Solution"])}
summary = {
    "reviewer": "/root/new_math_nr01",
    "scope": "Independent retained-evidence authentication only; no Lean, Lake, LeanCert, kernel replay, Comparator, sandbox or GitHub execution by this verifier.",
    "snapshot_sha256": sha(snapshot_bytes),
    "snapshot_files_authenticated": len(snap["files"]),
    "proof_import_closure_modules": len(sources),
    "full_body_read_mi27_files_matched": len(prep["source_hashes"]),
    "frozen_statement_files_unchanged": list(freeze["frozen_files"]),
    "local_receipts_authenticated": len(receipts),
    "modules_bound_to_fresh_success_and_current_olean": len(records),
    "actual_aggregate_axiom_reports": axioms,
    "actual_type_logs_equal": True,
    "actual_type_contracts": 20,
    "Linux_Comparator": "NOT_RUN; remains required separately",
    "publication_metadata": "Not in this source snapshot; separate review required",
    "module_records": records
}
(OUT / "EVIDENCE-AUDIT.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps({k:v for k,v in summary.items() if k not in ("actual_aggregate_axiom_reports","module_records")}, indent=2))
