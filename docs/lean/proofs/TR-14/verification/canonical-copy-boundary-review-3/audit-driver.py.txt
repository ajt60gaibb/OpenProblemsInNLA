#!/usr/bin/env python3
"""Independently check exact TR14 copies and the completed canonical boundary.

This is source/configuration evidence, not a substitute for the separate fresh
Lean consumer audit or authoritative Linux Comparator execution.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tomllib

REPO = Path(__file__).resolve().parents[5]
PROJECT = REPO / "tensor-computations/TR-14/lean"
SOURCE = REPO / "lean-statements"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--evidence-name", default="canonical-copy-boundary-review-3")
parser.add_argument("--manifest-python", default="/private/tmp/pr359-checks-venv/bin/python3")
args = parser.parse_args()
if Path(args.evidence_name).name != args.evidence_name:
    parser.error("--evidence-name must be a directory name")
evidence = Path(__file__).with_name(args.evidence_name)
evidence.mkdir(exist_ok=True)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def run(argv):
    p = subprocess.run(list(map(str, argv)), cwd=REPO, text=True, capture_output=True)
    return {"argv": list(map(str, argv)), "exit_code": p.returncode,
            "stdout": p.stdout, "stderr": p.stderr}

frozen = {str(p.relative_to(PROJECT)): p.read_bytes()
          for p in sorted(PROJECT.rglob("*")) if p.is_file()
          and ".lake" not in p.relative_to(PROJECT).parts}
lock = json.loads(frozen["proof-source-lock.json"])
boundary = json.loads(frozen["boundary-source-lock.json"])
checks = []
def check(name, passed, **details):
    checks.append({"name": name, "passed": bool(passed), **details})

ordered = []
visiting = set()
def visit(module):
    if module in ordered:
        return
    if module in visiting:
        raise RuntimeError("Cyclic local imports")
    visiting.add(module)
    data = (SOURCE / (module.replace(".", "/") + ".lean")).read_bytes()
    for imported in re.findall(r"^import\s+([A-Za-z0-9_.]+)\s*$", data.decode(), re.M):
        if (SOURCE / (imported.replace(".", "/") + ".lean")).is_file():
            visit(imported)
    visiting.remove(module)
    ordered.append(module)

visit("NLA.Proofs.TR14.Final")
check("exact-topological-source-closure", [r["module"] for r in lock["copies"]] == ordered,
      actual_module_count=len(ordered))
check("actual-source-and-proof-counts", len(ordered) == lock["topological_module_count"] == 78
      and sum(m.startswith("NLA.Proofs.TR14.") for m in ordered) == lock["proof_module_count"] == 76)
source_snapshots = {}
for record in lock["copies"]:
    relative = record["module"].replace(".", "/") + ".lean"
    data = (SOURCE / relative).read_bytes()
    source_snapshots[relative] = data
    imports = re.findall(r"^import\s+([A-Za-z0-9_.]+)\s*$", data.decode(), re.M)
    check("actual-exact-copy:" + relative,
          record["source"] == "lean-statements/" + relative
          and record["destination"] == "tensor-computations/TR-14/lean/" + relative
          and frozen.get(relative) == data
          and record["source_sha256"] == record["destination_sha256"] == sha(data)
          and record["imports"] == imports)
for name, digest in lock["package_exports"].items():
    check("current-export-lock:" + name, sha(frozen[name]) == digest)
expected_lean = {m.replace(".", "/") + ".lean" for m in ordered} | {
    "Reviewed/TR14.lean", "Challenge.lean", "Identity.lean", "Solution.lean"}
actual_lean = {name for name in frozen if name.endswith(".lean")}
check("exact-actual-lean-file-set", actual_lean == expected_lean,
      actual_lean_input_count=len(actual_lean), missing=sorted(expected_lean-actual_lean),
      extra=sorted(actual_lean-expected_lean))
for record in boundary["copies"]:
    check("historical-boundary-copy:" + record["package_path"],
          sha(frozen[record["package_path"]]) == record["sha256"]
          and frozen[record["package_path"]] == (REPO / record["source"]).read_bytes())
for name, digest in boundary["core"].items():
    if name != "lakefile.toml":
        check("historical-math-boundary:" + name, sha(frozen[name]) == digest)
old_lake_bytes = frozen["reviews/boundary-review-3-evidence/source/lakefile.toml.txt"]
old_lake = tomllib.loads(old_lake_bytes.decode())
new_lake = tomllib.loads(frozen["lakefile.toml"].decode())
check("retained-original-lakefile", sha(old_lake_bytes) == boundary["core"]["lakefile.toml"])
new_without_solution = dict(new_lake)
new_without_solution["defaultTargets"] = [n for n in new_lake["defaultTargets"] if n != "Solution"]
new_without_solution["lean_lib"] = [r for r in new_lake["lean_lib"] if r != {"name": "Solution"}]
check("lake-extension-only-solution", new_without_solution == old_lake
      and new_lake["defaultTargets"].count("Solution") == 1
      and new_lake["lean_lib"].count({"name": "Solution"}) == 1)
check("exact-single-target-comparator", json.loads(frozen["comparator.json"]) == {
    "challenge_module": "Challenge", "solution_module": "Solution",
    "theorem_names": ["NLA.TR14.target"], "definition_names": [],
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]})
check("literal-final-solution-wrapper", frozen["Solution.lean"].decode() == '''import NLA.Proofs.TR14.Final

/-! Complete unchanged TR-14 target, discharged by the exact copied proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.TR14

theorem target : NLA.Statements.TR14.Target := by
  exact NLA.Proofs.TR14.target

#assert_trust kernel target
#print axioms target

end NLA.TR14
''')
check("solution-independent-of-challenge", not re.search(r"^import\s+Challenge\b", frozen["Solution.lean"].decode(), re.M))
approval3 = json.loads(frozen["reviews/PRE_SOLUTION_APPROVAL_3.json"])
check("pre-solution-approval-3", approval3.get("fresh_audit_passed") is True
      and approval3.get("Solution_absent_during_review") is True
      and approval3.get("reviewer_is_package_author") is False
      and approval3.get("boundary_source_lock_sha256") == sha(frozen["boundary-source-lock.json"]))
approval2 = json.loads(frozen["reviews/boundary-review-2-evidence/result.json"])
check("pre-solution-boundary-2", approval2.get("solution_absent") is True
      and approval2.get("lock_sha256") == sha(frozen["boundary-source-lock.json"])
      and all(r["pass"] for r in approval2["copy_checks"] + approval2["core_checks"] + approval2["dependencies"])
      and len(approval2["builds"]) == 5 and all(r["exit_code"] == 0 for r in approval2["builds"])
      and approval2["negative_control"]["expected_rejection"] is True
      and approval2["negative_control"]["exit_code"] != 0
      and approval2["negative_control"]["reason"] == "sorryAx")
check("pre-solution-boundary-3", json.loads(frozen["reviews/boundary-review-3-evidence/result.json"]).get("passed") is True)
manifest = run([args.manifest_python, REPO / "tools/lean/validate_manifest.py", PROJECT])
check("real-manifest-schema-and-coverage", manifest["exit_code"] == 0, command=manifest)
check("canonical-id-path-preserved", json.loads((REPO / "problem_ids.json").read_text())["TR-14"]
      == "tensor-computations/TR-14/README.md")
for name, data in frozen.items():
    if name.endswith(".lean") or name in {"proof-source-lock.json", "boundary-source-lock.json",
        "comparator.json", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        "formalization.yaml", "README.md", "reviews/PRE_SOLUTION_APPROVAL_3.json"}:
        destination = evidence / "source" / (name + ".txt")
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
(evidence / "audit-driver.py.txt").write_bytes(Path(__file__).read_bytes())
unchanged = {name: (PROJECT / name).read_bytes() == data for name, data in frozen.items()}
source_unchanged = {name: (SOURCE / name).read_bytes() == data for name, data in source_snapshots.items()}
result = {"scope": "Independent exact-copy, complete-source-set and preserved mathematical Comparator boundary review; separate Lean/Linux evidence required",
          "reviewer": "/root/lean_verification", "self_authored_TR14_modules": [],
          "project": str(PROJECT), "checks": checks,
          "source_sha256": {name: sha(data) for name, data in frozen.items()},
          "shared_source_sha256": {name: sha(data) for name, data in source_snapshots.items()},
          "package_unchanged_after": unchanged, "shared_source_unchanged_after": source_unchanged,
          "linux_comparator": False,
          "passed": all(c["passed"] for c in checks) and all(unchanged.values()) and all(source_unchanged.values())}
(evidence / "result.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": result["passed"], "checks": len(checks),
                  "failed": [c["name"] for c in checks if not c["passed"]]}, indent=2))
raise SystemExit(0 if result["passed"] else 1)
