#!/usr/bin/env python3
"""Independently elaborate the frozen TR06 specification before Solution.

Challenge's eleven sorry bodies are intentional specifications, not proofs.
Only the actual Identity theorem is subjected to proof-kind/kernel acceptance.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--lean", type=Path, required=True)
parser.add_argument("--packages", type=Path, required=True)
args = parser.parse_args()
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
PROJECT = REPO / "tensor-computations/TR-06/lean"
LEAN = args.lean.resolve()
PACKAGES = args.packages.resolve()
RESULT = HERE / "fresh-boundary-result.json"
if RESULT.exists():
    raise RuntimeError("Refusing to overwrite completed boundary evidence")

def sha(data):
    return hashlib.sha256(data).hexdigest()

def run(argv, **kwargs):
    proc = subprocess.run(list(map(str, argv)), capture_output=True, text=True, **kwargs)
    return {"argv": list(map(str, argv)), "exit_code": proc.returncode,
            "stdout": proc.stdout, "stderr": proc.stderr}

def dependencies():
    result = []
    for item in json.loads((PROJECT / "lake-manifest.json").read_text())["packages"]:
        path = PACKAGES / item["name"]
        head = run(["git", "-C", path, "rev-parse", "HEAD"])
        status = run(["git", "-C", path, "status", "--porcelain", "--untracked-files=no"])
        result.append({"name": item["name"], "expected_revision": item["rev"],
                       "head": head, "status": status,
                       "passed": head["exit_code"] == status["exit_code"] == 0
                       and head["stdout"].strip() == item["rev"]
                       and not status["stdout"].strip()})
    return result

lock = json.loads((HERE.parent / "source-lock.json").read_text())
snapshots = {row["path"]: (HERE / "source" / (row["path"] + ".txt")).read_bytes()
             for row in lock["records"]}
if len(snapshots) != 70 or any(sha(snapshots[row["path"]]) != row["sha256"]
                               for row in lock["records"]):
    raise RuntimeError("Frozen 70-input snapshots do not match their reviewed lock")
if any((PROJECT / name).read_bytes() != data for name, data in snapshots.items()):
    raise RuntimeError("Canonical inputs changed before the independent review")
if (PROJECT / "Solution.lean").exists():
    raise RuntimeError("This audit must run before Solution exists")
names = ["NLA/Statements/Infrastructure.lean", "NLA/Statements/TR06.lean",
         "Reviewed/TR06.lean", "NLA/TR06/Definitions.lean", "Challenge.lean", "Identity.lean"]
consumer = '''import Challenge
import Identity
import LeanCert.Tactic.Verification
open Lean Elab Command in
elab "#assert_actual_proof_constant " n:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? decl with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "expected an actual theorem constant"
open Lean Elab Command in
elab "#assert_literal_challenge_target " n:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? decl with
  | some (.thmInfo info) =>
    unless info.type == mkConst ``NLA.Statements.TR06.Target do
      throwErrorAt n "expected the literal intrinsic Target, with no added hypotheses"
  | _ => throwErrorAt n "expected an intentional challenge theorem placeholder"
#assert_literal_challenge_target NLA.TR06.target
#assert_actual_proof_constant NLA.TR06.target_eq_reviewed
#assert_trust kernel NLA.TR06.target_eq_reviewed
#print axioms NLA.TR06.target_eq_reviewed
-- This print intentionally exposes sorryAx in the comparison specification.
-- No Challenge placeholder is accepted as a proof.
#print axioms NLA.TR06.target
'''
(HERE / "IndependentBoundary.lean.txt").write_text(consumer)
before = dependencies()
if len(before) != 10 or not all(row["passed"] for row in before):
    raise RuntimeError("Pinned dependency identity/cleanliness check failed")
result = {"reviewer": "/root/recover_verification", "scope": __doc__,
          "solution_absent_before": not (PROJECT / "Solution.lean").exists(),
          "source_lock_sha256": sha((HERE.parent / "source-lock.json").read_bytes()),
          "driver_sha256": sha(Path(__file__).read_bytes()),
          "lean_version": run([LEAN, "--version"]), "lean_sha256": sha(LEAN.read_bytes()),
          "dependencies_before": before, "commands": [],
          "consumer_sha256": sha(consumer.encode()), "authoritative_linux_comparator": False,
          "full_Target_proved": False}
with tempfile.TemporaryDirectory(prefix="tr06-independent-pre-solution-") as temporary:
    base = Path(temporary)
    source, output = base / "source", base / "output"
    for name in names:
        path = source / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(snapshots[name])
    (source / "IndependentBoundary.lean").write_text(consumer)
    output.mkdir()
    libraries = [p / ".lake/build/lib/lean" for p in sorted(PACKAGES.iterdir())
                 if (p / ".lake/build/lib/lean").is_dir()]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str,
               [output, *libraries, LEAN.parent.parent / "lib/lean"])))
    result["lean_path"] = env["LEAN_PATH"]
    for name in names + ["IndependentBoundary.lean"]:
        obj = output / Path(name).with_suffix(".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        record = run([LEAN, "-R", source, "-o", obj, source / name],
                     cwd=source, env=env, timeout=180)
        record["source"] = name
        result["commands"].append(record)
        (HERE / (name.replace("/", "-") + ".log")).write_text(record["stdout"] + record["stderr"])
        print(name, record["exit_code"], flush=True)
        if record["exit_code"]:
            break
result["dependencies_after"] = dependencies()
result["all_70_inputs_unchanged_after"] = all((PROJECT / name).read_bytes() == data
                                               for name, data in snapshots.items())
result["solution_absent_after"] = not (PROJECT / "Solution.lean").exists()
result["passed"] = (len(result["commands"]) == 7
                    and all(row["exit_code"] == 0 for row in result["commands"])
                    and all(row["passed"] for row in result["dependencies_after"])
                    and result["all_70_inputs_unchanged_after"]
                    and result["solution_absent_before"] and result["solution_absent_after"])
RESULT.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": result["passed"], "commands": len(result["commands"])}, indent=2))
raise SystemExit(0 if result["passed"] else 1)
