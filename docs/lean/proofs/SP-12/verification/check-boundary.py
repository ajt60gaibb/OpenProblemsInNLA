#!/usr/bin/env python3
"""Independently audit the frozen SP12 Comparator scaffold, not a target proof."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

REPO = Path(__file__).resolve().parents[5]
PROJECT = REPO / "eigenvalues-and-inverse-problems/SP-12/lean"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--snapshot", type=Path, help="Replay the original scaffold's retained *.txt source snapshots")
parser.add_argument("--evidence-name", default="boundary-review")
args = parser.parse_args()
if Path(args.evidence_name).name != args.evidence_name:
    parser.error("--evidence-name must be a directory name")
EVIDENCE = Path(__file__).with_name(args.evidence_name)
LEAN = Path("/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin/lean")
PACKAGES = Path("/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages")
EVIDENCE.mkdir(exist_ok=True)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(argv, **kwargs):
    p = subprocess.run(list(map(str, argv)), text=True, capture_output=True, **kwargs)
    return {"argv": list(map(str, argv)), "exit_code": p.returncode,
            "stdout": p.stdout, "stderr": p.stderr}


if args.snapshot:
    ignored = {"IndependentBoundaryConsumer.lean", "RejectChallengePlaceholder.lean"}
    source_inputs = {str(p.relative_to(args.snapshot))[:-4]: p for p in sorted(args.snapshot.rglob("*.txt"))
                     if str(p.relative_to(args.snapshot))[:-4] not in ignored}
else:
    source_inputs = {str(p.relative_to(PROJECT)): p for p in sorted(PROJECT.rglob("*"))
                     if p.is_file() and ".lake" not in p.relative_to(PROJECT).parts}
frozen = {name: path.read_bytes() for name, path in source_inputs.items()}
lock = json.loads(frozen["boundary-source-lock.json"])
checks = []
for record in lock["copies"]:
    actual = frozen[record["package_path"]]
    checks.append({"name": "copied-source:" + record["package_path"],
                   "passed": sha(actual) == record["sha256"]
                   and actual == (REPO / record["source"]).read_bytes()})
for name, digest in lock["core"].items():
    checks.append({"name": "boundary-lock:" + name, "passed": sha(frozen[name]) == digest})
comparator = json.loads(frozen["comparator.json"])
checks.append({"name": "exact-single-theorem-boundary", "passed": comparator == {
    "challenge_module": "Challenge", "solution_module": "Solution",
    "theorem_names": ["NLA.SP12.target"], "definition_names": [],
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]}})
checks.append({"name": "solution-absent", "passed": "Solution.lean" not in frozen})
def dependency_pins(manifest):
    # Inheritance and requested input refs describe package topology, not the
    # resolved source identity. The canonical package directly requires Mathlib.
    return {item["name"]: {k: item.get(k) for k in ["url", "type", "subDir", "rev"]}
            for item in manifest["packages"]}


checks.append({"name": "same-package-dependency-pins", "passed":
    dependency_pins(json.loads(frozen["lake-manifest.json"])) ==
    dependency_pins(json.loads((REPO / "lean-statements/lake-manifest.json").read_text()))})
dependency_records = []
for item in json.loads(frozen["lake-manifest.json"])["packages"]:
    directory = PACKAGES / item["name"]
    head = run(["git", "-C", directory, "rev-parse", "HEAD"])
    status = run(["git", "-C", directory, "status", "--porcelain", "--untracked-files=no"])
    dependency_records.append({"name": item["name"], "expected_revision": item["rev"],
                               "head": head, "status": status,
                               "passed": head["exit_code"] == status["exit_code"] == 0
                               and head["stdout"].strip() == item["rev"] and not status["stdout"].strip()})
positive = '''import Challenge
import Identity
import LeanCert.Tactic.Verification
#check NLA.SP12.target
#check NLA.SP12.target_eq_reviewed
#assert_trust kernel NLA.SP12.target_eq_reviewed
#print axioms NLA.SP12.target_eq_reviewed
open Lean Elab Command in
elab "#require_target_theorem" : command => do
  match (← getEnv).find? `NLA.SP12.target with
  | some (.thmInfo _) => pure ()
  | _ => throwError "target must be a theorem constant"
#require_target_theorem
'''
negative = '''import Challenge
import LeanCert.Tactic.Verification
#assert_trust kernel NLA.SP12.target
'''
build_sources = ["NLA/Statements/Infrastructure.lean", "NLA/Statements/SP12.lean",
                 "Reviewed/SP12.lean", "Challenge.lean", "Identity.lean"]
sources = {name: frozen[name] for name in build_sources}
sources["IndependentBoundaryConsumer.lean"] = positive.encode()
sources["RejectChallengePlaceholder.lean"] = negative.encode()
for name, data in {**frozen, **sources}.items():
    target = EVIDENCE / "source" / (name + ".txt")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
result = {"scope": ("Historical frozen scaffold snapshot replay; current completed package is outside this check"
                    if args.snapshot else "Exact frozen Comparator statement scaffold only; Challenge is deliberately unproved"),
          "reviewer": "/root/lean_verification", "source_sha256": {n: sha(b) for n, b in frozen.items()},
          "historical_source_snapshot": str(args.snapshot) if args.snapshot else None,
          "checks": checks, "dependencies": dependency_records,
          "lean_version": run([LEAN, "--version"]), "lean_sha256": sha(LEAN.read_bytes()),
          "commands": [], "full_target_proved": False, "linux_comparator": False}
with tempfile.TemporaryDirectory(prefix="nla-sp12-package-boundary-") as temporary:
    root = Path(temporary)
    src, out = root / "source", root / "output"
    for name, data in sources.items():
        target = src / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    out.mkdir()
    libs = [p / ".lake/build/lib/lean" for p in sorted(PACKAGES.iterdir())
            if (p / ".lake/build/lib/lean").is_dir()]
    env = dict(os.environ, LEAN_PATH=":".join(map(str, [out, *libs, LEAN.parent.parent / "lib/lean"])))
    for name in sources:
        output = out / Path(name).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        record = run([LEAN, "-R", src, "-o", output, src / name], cwd=src, env=env, timeout=120)
        record["source"] = name
        record["expected_rejection"] = name == "RejectChallengePlaceholder.lean"
        result["commands"].append(record)
        (EVIDENCE / (name.replace("/", "-") + ".log")).write_text(record["stdout"] + record["stderr"])
        print(name, record["exit_code"], flush=True)
result["source_unchanged_after"] = {n: source_inputs[n].read_bytes() == b for n, b in frozen.items()}
result["solution_still_absent"] = (not (args.snapshot / "Solution.lean.txt").exists()
                                   if args.snapshot else not (PROJECT / "Solution.lean").exists())
result["current_package_solution_exists"] = (PROJECT / "Solution.lean").exists()
result["passed"] = (all(c["passed"] for c in checks + dependency_records)
                    and all(result["source_unchanged_after"].values())
                    and result["solution_still_absent"]
                    and all(c["exit_code"] == 0 for c in result["commands"][:-1])
                    and result["commands"][-1]["exit_code"] != 0
                    and "sorryAx" in result["commands"][-1]["stdout"])
(EVIDENCE / "result.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": result["passed"], "checks": len(checks), "commands": len(result["commands"])}, indent=2))
raise SystemExit(0 if result["passed"] else 1)
