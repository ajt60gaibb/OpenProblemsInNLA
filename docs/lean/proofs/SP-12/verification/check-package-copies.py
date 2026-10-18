#!/usr/bin/env python3
"""Check the completed canonical SP12 proof copies against shared and frozen inputs."""
import hashlib
import json
import tomllib
from pathlib import Path

REPO = Path(__file__).resolve().parents[5]
PROJECT = REPO / "eigenvalues-and-inverse-problems/SP-12/lean"
OUT = Path(__file__).with_name("canonical-copy-review.json")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


checks = []


def check(name, passed, **details):
    checks.append({"name": name, "passed": bool(passed), **details})


lock = json.loads((PROJECT / "proof-source-lock.json").read_text())
boundary = json.loads((PROJECT / "boundary-source-lock.json").read_text())
copies = []
for item in lock["copies"]:
    source, destination = REPO / item["source"], REPO / item["destination"]
    good = sha(source) == sha(destination) == item["source_sha256"] == item["destination_sha256"]
    copies.append({"source": item["source"], "destination": item["destination"],
                   "sha256": sha(source), "passed": good})
check("all-51-copies-exact", len(copies) == 51 and all(x["passed"] for x in copies))
check("48-proof-modules", sum("/Proofs/" in x["source"] for x in copies) == 48)
exports = [{"path": name, "sha256": sha(PROJECT / name),
            "passed": sha(PROJECT / name) == digest}
           for name, digest in lock["package_exports"].items()]
check("all-locked-exports", all(x["passed"] for x in exports))
expected = {str((REPO / x["destination"]).relative_to(PROJECT)) for x in copies}
expected |= {"Solution.lean", "Identity.lean", "Challenge.lean", "Reviewed/SP12.lean"}
actual = {str(p.relative_to(PROJECT)) for p in PROJECT.rglob("*.lean")
          if ".lake" not in p.relative_to(PROJECT).parts}
check("exact-55-Lean-inputs", len(actual) == 55 and actual == expected,
      added=sorted(actual-expected), missing=sorted(expected-actual))
preserved = []
for item in boundary["copies"]:
    preserved.append({"path": item["package_path"],
                      "passed": sha(PROJECT / item["package_path"]) == item["sha256"]
                      and (PROJECT / item["package_path"]).read_bytes() == (REPO / item["source"]).read_bytes()})
for name, digest in boundary["core"].items():
    if name != "lakefile.toml":
        preserved.append({"path": name, "passed": sha(PROJECT / name) == digest})
check("frozen-math-boundary-unchanged", all(x["passed"] for x in preserved))
old = (Path(__file__).with_name("boundary-review") / "source/lakefile.toml.txt").read_text()
new = (PROJECT / "lakefile.toml").read_text()
old_config, new_config = tomllib.loads(old), tomllib.loads(new)
old_config["defaultTargets"].append("Solution")
old_config["lean_lib"][0]["globs"].insert(1, "NLA.Proofs.SP11.+")
old_config["lean_lib"].append({"name": "Solution"})
check("lakefile-adds-only-proof-prerequisite-and-solution-library", new_config == old_config)
config = json.loads((PROJECT / "comparator.json").read_text())
check("exact-single-full-target-no-holes", config == {
    "challenge_module": "Challenge", "solution_module": "Solution",
    "theorem_names": ["NLA.SP12.target"], "definition_names": [],
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]})
solution = (PROJECT / "Solution.lean").read_text()
check("literal-target-wrapper", "theorem target : NLA.Statements.SP12.Target := by\n  exact NLA.Proofs.SP12.target" in solution)
check("canonical-original-page-identical", (PROJECT / "ORIGINAL.md").read_bytes() ==
      (REPO / "eigenvalues-and-inverse-problems/SP-12/README.md").read_bytes())
approval1 = json.loads((PROJECT / "reviews/PRE_SOLUTION_APPROVAL_1.json").read_text())
approval2 = json.loads((Path(__file__).with_name("boundary-review") / "result.json").read_text())
check("two-retained-pre-solution-approvals", approval1["Solution_absent_during_review"]
      and approval1["approval"].startswith("PASS") and approval2["passed"]
      and approval2["solution_still_absent"])
result = {"reviewer": "/root/lean_verification", "scope": "Completed package exact copies and preserved frozen comparison boundary; not Linux acceptance",
          "self_authored_SP12_modules": [], "proof_source_lock_sha256": sha(PROJECT / "proof-source-lock.json"),
          "boundary_source_lock_sha256": sha(PROJECT / "boundary-source-lock.json"),
          "checks": checks, "copies": copies, "exports": exports, "preserved_boundary": preserved,
          "passed": all(x["passed"] for x in checks)}
OUT.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": result["passed"], "checks": len(checks), "failed": [x["name"] for x in checks if not x["passed"]]}, indent=2))
raise SystemExit(0 if result["passed"] else 1)
