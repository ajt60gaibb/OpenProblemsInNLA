#!/usr/bin/env python3
"""Exercise pinned Comparator comparison/axiom code locally, with no sandbox claim.

This invokes the unchanged Comparator library APIs on separately imported Lean
fixture environments. It does not invoke the Linux executable, its exporter,
sandbox, or raw-kernel replay. No IE-06 theorem is proved by these controls.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import pathlib
import platform
import shutil
import subprocess
import tempfile
import time

PROJECT = pathlib.Path(__file__).resolve().parents[1]
REPOSITORY = PROJECT.parents[2]
ARCHIVE = REPOSITORY / "eigenvalues-and-inverse-problems/IS-03/lean/verification/linux-2026-09-12/source/forsythe"
PINNED = [
    (".tools/lean4export/Export/Parse.lean", "Export/Parse.lean"),
    (".tools/comparator/Comparator/Util.lean", "Comparator/Util.lean"),
    (".tools/comparator/Comparator/Axioms.lean", "Comparator/Axioms.lean"),
    (".tools/comparator/Comparator/Compare.lean", "Comparator/Compare.lean"),
]
PRELUDE = "import Lean.Elab.Tactic.Decide\ndef meaning : Prop := (1 : Nat) = 1\n"
FIXTURES = {
    "FixtureChallenge": PRELUDE + "theorem claim : meaning := by sorry\n",
    "FixtureMatch": PRELUDE + "theorem claim : meaning := rfl\n",
    "FixtureMismatch": PRELUDE + "theorem claim : True := True.intro\n",
    "FixtureChangedDefinition": PRELUDE.replace("(1 : Nat) = 1", "(2 : Nat) = 2") + "theorem claim : meaning := rfl\n",
    "FixtureKindMismatch": PRELUDE + "axiom claim : meaning\n",
    "FixtureSorry": PRELUDE + "theorem claim : meaning := by sorry\n",
    "FixtureNative": PRELUDE + "theorem claim : meaning := by native_decide\n",
}
RUNNER = r'''import Lean
import Comparator.Compare

open Lean

def imported (moduleName : Name) : IO Export.ExportedEnv := do
  let env ← importModules #[{ module := moduleName }] {} 0
  let consts := env.constants.toList
  return { constMap := Std.HashMap.ofList consts, constOrder := (consts.map Prod.fst).toArray }

def requireSuccess (label : String) (result : Except String Unit) : IO Unit := do
  match result with
  | .ok _ => IO.println s!"PASS {label}"
  | .error err => throw <| IO.userError s!"{label}: unexpected rejection: {err}"

def requireRejection (label needle : String) (result : Except String Unit) : IO Unit := do
  match result with
  | .ok _ => throw <| IO.userError s!"{label}: unexpectedly accepted"
  | .error err =>
    if (err.splitOn needle).length < 2 then
      throw <| IO.userError s!"{label}: unexpected rejection reason: {err}"
    IO.println s!"PASS {label}: {err}"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← imported `FixtureChallenge
  let matching ← imported `FixtureMatch
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  requireSuccess "matching theorem and definition" <|
    Comparator.compareAt challenge matching #[`claim] #[] #[]
  requireSuccess "matching theorem permitted axioms" <|
    Comparator.checkAxioms matching #[`claim] #[] allowed
  let mismatch ← imported `FixtureMismatch
  requireRejection "different theorem type" "theorem statement do not match" <|
    Comparator.compareAt challenge mismatch #[`claim] #[] #[]
  let changed ← imported `FixtureChangedDefinition
  requireRejection "changed meaning behind same theorem type" "Const does not match" <|
    Comparator.compareAt challenge changed #[`claim] #[] #[]
  let kindMismatch ← imported `FixtureKindMismatch
  requireRejection "theorem replaced by axiom" "constant kind don't match" <|
    Comparator.compareAt challenge kindMismatch #[`claim] #[] #[]
  let admitted ← imported `FixtureSorry
  requireSuccess "admitted theorem still has matching statement" <|
    Comparator.compareAt challenge admitted #[`claim] #[] #[]
  requireRejection "sorry proof axiom" "Illegal axiom detected: 'sorryAx'" <|
    Comparator.checkAxioms admitted #[`claim] #[] allowed
  let native ← imported `FixtureNative
  requireSuccess "native theorem still has matching statement" <|
    Comparator.compareAt challenge native #[`claim] #[] #[]
  requireRejection "native execution axiom" "Illegal axiom detected:" <|
    Comparator.checkAxioms native #[`claim] #[] allowed
  IO.println "All nine Comparator-core fixture assertions passed."
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, type=pathlib.Path)
    args = parser.parse_args()
    lean = args.lean.resolve()
    evidence = PROJECT / "verification/comparator-core"
    evidence.mkdir(parents=True, exist_ok=True)
    attempt = pathlib.Path(tempfile.mkdtemp(prefix="attempt-", dir=evidence))
    source = attempt / "source"
    source.mkdir()
    build = pathlib.Path(tempfile.mkdtemp(prefix="nla-ie06-comparator-core-"))
    result = {"phase": "local Comparator core library fixture checks", "pass": False,
              "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "platform": platform.platform(), "commands": [], "pinned_sources": {},
              "comparator_core_executed": False, "full_comparator_executed": False,
              "exporter_executed": False, "raw_kernel_replay_executed": False,
              "authoritative_linux_sandbox": False, "ie06_targets_proved": False,
              "script_sha256": sha(pathlib.Path(__file__))}
    try:
        version = subprocess.check_output([str(lean), "--version"], text=True).strip()
        if "version 4.33.1," not in version:
            raise RuntimeError("Expected Lean 4.33.1")
        result["lean_version"] = version
        result["lean_executable_sha256"] = sha(lean)
        lock_path = REPOSITORY / "tools/lean/source-lock.json"
        result["source_lock_sha256"] = sha(lock_path)
        lock = {f["destination"]: f for f in json.loads(lock_path.read_text())["files"]}
        for old, new in PINNED + [(".tools/comparator/LICENSE", "LICENSE-COMPARATOR")]:
            src, dst = ARCHIVE / old, source / new
            if sha(src) != lock[old]["sha256"] or src.stat().st_size != lock[old]["bytes"]:
                raise RuntimeError(f"Source-lock mismatch: {src}")
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src, dst)
            result["pinned_sources"][new] = {"source": str(src.relative_to(REPOSITORY)), "sha256": sha(src)}
        for name, content in FIXTURES.items():
            (source / f"{name}.lean").write_text(content)
        (source / "RunCore.lean").write_text(RUNNER)
        shutil.copyfile(__file__, source / "check_comparator_core.py")
        env = os.environ.copy()
        env["PATH"] = str(lean.parent) + os.pathsep + env.get("PATH", "")
        env["LEAN_PATH"] = os.pathsep.join([str(build), str(lean.parent.parent / "lib/lean")])

        def run(rel, execute=False):
            artifact = build / pathlib.Path(rel).with_suffix(".olean")
            artifact.parent.mkdir(parents=True, exist_ok=True)
            cmd = [str(lean), "--run", rel] if execute else [str(lean), "-o", str(artifact), rel]
            started = time.monotonic()
            cp = subprocess.run(cmd, cwd=source, env=env, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=180)
            log = attempt / (rel.replace("/", "-") + ".log")
            log.write_text(cp.stdout)
            result["commands"].append({"argv": cmd, "exit_code": cp.returncode,
                                        "elapsed_seconds": time.monotonic() - started,
                                        "log": log.name, "log_sha256": sha(log)})
            print(json.dumps(result["commands"][-1]), flush=True)
            if cp.returncode:
                raise RuntimeError(f"Command failed: {cmd}; see {log}")
            return cp.stdout

        for _, rel in PINNED:
            run(rel)
        for name in FIXTURES:
            run(name + ".lean")
        final = run("RunCore.lean", execute=True)
        if "All nine Comparator-core fixture assertions passed." not in final:
            raise RuntimeError("Missing successful completion assertion")
        result["comparator_core_executed"] = True
        result["pass"] = True
    except Exception as exc:
        result["error"] = str(exc)
    finally:
        result["snapshot"] = {str(p.relative_to(source)): {"sha256": sha(p), "bytes": p.stat().st_size}
                              for p in source.rglob("*") if p.is_file()}
        shutil.rmtree(build)
        result["temporary_compiled_objects_removed"] = not build.exists()
        receipt = attempt / "result.json"
        receipt.write_text(json.dumps(result, indent=2) + "\n")
        (evidence / "latest.json").write_text(json.dumps({"attempt": attempt.name,
                            "result_sha256": sha(receipt)}, indent=2) + "\n")
        print(json.dumps({"attempt": str(attempt), "pass": result["pass"], "error": result.get("error")}), flush=True)
    raise SystemExit(0 if result["pass"] else 1)


if __name__ == "__main__":
    main()
