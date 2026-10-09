#!/usr/bin/env python3
"""Check a fresh source snapshot using pinned, read-only local dependency caches.

This development check is deliberately separate from tools/lean/verify.sh. It
does not provide Linux sandbox isolation, exporter execution, or raw kernel
replay. Optional --compare-solution runs the pinned Comparator library on the
actual six Challenge/Solution theorem names after fresh compilation and the
owned-declaration axiom audit. Challenge holes remain reference signatures.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import pathlib
import platform
import re
import shutil
import subprocess
import tempfile
import time

PROJECT = pathlib.Path(__file__).resolve().parents[1]
REPOSITORY = PROJECT.parents[2]
FOUNDATIONAL = ["propext", "Classical.choice", "Quot.sound"]
TARGET_THEOREMS = [
    "NLA.IE06.squareRootUpperBound",
    "NLA.IE06.schurSubpolynomialTail",
    "NLA.IE06.gaussianMatrix_probability",
    "NLA.IE06.exceedanceEvent_measurable",
    "NLA.IE06.admissiblePath_exists",
    "NLA.IE06.gaussianMatrix_singular_null",
]
COMPARATOR_ARCHIVE = REPOSITORY / "eigenvalues-and-inverse-problems/IS-03/lean/verification/linux-2026-09-12/source/forsythe"
COMPARATOR_PINNED = [
    (".tools/lean4export/Export/Parse.lean", "Export/Parse.lean"),
    (".tools/comparator/Comparator/Util.lean", "Comparator/Util.lean"),
    (".tools/comparator/Comparator/Axioms.lean", "Comparator/Axioms.lean"),
    (".tools/comparator/Comparator/Compare.lean", "Comparator/Compare.lean"),
]
COMPARATOR_COMPLETION = "All six actual IE-06 Challenge/Solution theorem comparisons and axiom checks passed."


def comparator_runner(config):
    """Generate a runner only from the exact fixed six-target manifest."""
    expected = {"challenge_module": "Challenge", "solution_module": "Solution",
                "theorem_names": TARGET_THEOREMS, "definition_names": [],
                "permitted_axioms": FOUNDATIONAL}
    if config != expected:
        raise RuntimeError("Comparator manifest must specify exactly the six canonical IE-06 theorems, "
                           "Challenge/Solution, no definition holes, and foundational axioms only")
    names = ", ".join("`" + name for name in config["theorem_names"])
    axioms = ", ".join("`" + name for name in config["permitted_axioms"])
    # Neither mathematical module is imported into the runner environment.
    # importModules constructs a separate environment for each actual module.
    return r'''import Lean
import Comparator.Compare

open Lean

def imported (moduleName : Name) : IO Export.ExportedEnv := do
  let env ← importModules #[{ module := moduleName }] {} 0
  let consts := env.constants.toList
  return { constMap := Std.HashMap.ofList consts, constOrder := (consts.map Prod.fst).toArray }

def requireSuccess (label : String) (result : Except String Unit) : IO Unit := do
  match result with
  | .ok _ => IO.println s!"PASS {label}"
  | .error err => throw <| IO.userError s!"{label}: rejected: {err}"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← imported `Challenge
  let solution ← imported `Solution
''' + f'''  let names := #[{names}]
  let allowed := #[{axioms}]
''' + r'''  for name in names do
    requireSuccess s!"actual theorem statement and referenced definitions: {name}" <|
      Comparator.compareAt challenge solution #[name] #[] #[]
    requireSuccess s!"actual theorem transitive proof axioms: {name}" <|
      Comparator.checkAxioms solution #[name] #[] allowed
''' + f'  IO.println "{COMPARATOR_COMPLETION}"\n'



def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def output(argv, **kwargs):
    return subprocess.check_output(argv, text=True, **kwargs).strip()


def dependencies(packages):
    manifest = json.loads((PROJECT / "lake-manifest.json").read_text())
    records = []
    paths = []
    for package in manifest["packages"]:
        directory = packages / package["name"]
        # One preexisting local cache uses a case-sensitive LeanCert directory.
        if not directory.is_dir() and package["name"] == "leancert":
            directory = packages / "LeanCert"
        head = output(["git", "-C", str(directory), "rev-parse", "HEAD"])
        dirty = output(["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"])
        if head != package["rev"] or dirty:
            raise RuntimeError(f"Dependency pin/cleanliness failed: {package['name']}: {head}: {dirty}")
        lib = directory / ".lake/build/lib/lean"
        if not lib.is_dir() and package["name"] != "Cli":
            raise RuntimeError(f"Missing compiled dependency cache: {lib}")
        if lib.is_dir():
            paths.append(str(lib))
        records.append({"name": package["name"], "directory": str(directory),
                        "revision": head, "tracked_sources_clean": True,
                        "compiled_cache_present": lib.is_dir()})
    return paths, records


def order_sources(sources, snapshot):
    modules = {str(p.with_suffix("")).replace(os.sep, "."): p for p in sources}
    completed, active, ordered = set(), set(), []

    def visit(name):
        if name in completed:
            return
        if name in active:
            raise RuntimeError(f"Local import cycle: {name}")
        active.add(name)
        for imported in re.findall(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_'.]+)",
                                   (snapshot / modules[name]).read_text(), re.M):
            if imported in modules:
                visit(imported)
        active.remove(name)
        completed.add(name)
        ordered.append(modules[name])

    for module in sorted(modules):
        visit(module)
    return ordered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=shutil.which("lean"),
                        help="Absolute Lean 4.33.1 executable")
    parser.add_argument("--packages", type=pathlib.Path, required=True,
                        help="Read-only dependency cache matching lake-manifest.json")
    parser.add_argument("--infrastructure-only", action="store_true")
    parser.add_argument("--compare-solution", action="store_true",
                        help="Compare the six actual Challenge/Solution theorem targets with the pinned Comparator library")
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()
    if args.compare_solution and args.infrastructure_only:
        parser.error("--compare-solution requires the full source build, not --infrastructure-only")
    if not args.lean:
        parser.error("Lean is not on PATH; supply --lean")
    lean = pathlib.Path(args.lean).resolve()
    packages = args.packages.resolve()
    evidence = PROJECT / "verification/local"
    evidence.mkdir(parents=True, exist_ok=True)
    attempt = pathlib.Path(tempfile.mkdtemp(prefix="attempt-", dir=evidence))
    snapshot = attempt / "source"
    snapshot.mkdir()
    result = {
        "phase": ("local actual Solution proof comparison" if args.compare_solution else
                  "local infrastructure check" if args.infrastructure_only else "local statement elaboration"),
        "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "platform": platform.platform(), "argv": list(__import__("sys").argv),
        "commands": [], "inputs": {}, "pass": False,
        "authoritative_linux_comparator": False, "comparator_executed": False,
        "ie06_targets_proved": False,
        "compare_solution_requested": args.compare_solution,
        "comparator_core_executed": False, "full_comparator_executed": False,
        "authoritative_linux_sandbox": False,
        "exporter_executed": False, "raw_kernel_replay_executed": False,
        "actual_targets_kernel_proof_checked": False,
        "challenge_holes_are_reference_signatures_only": True,
        "cache_limit": "Tracked sources/pins checked; compiled dependency cache is trusted local development input.",
    }
    build = pathlib.Path(tempfile.mkdtemp(prefix="nla-ie06-local-"))
    try:
        if args.compare_solution and not (PROJECT / "Solution.lean").is_file():
            raise RuntimeError("--compare-solution requires actual Solution.lean; Challenge signatures or fixtures are not solutions")
        result["lean_version"] = output([str(lean), "--version"])
        if "version 4.33.1," not in result["lean_version"]:
            raise RuntimeError("Expected Lean 4.33.1")
        result["lean_executable_sha256"] = sha(lean)
        libs, result["dependencies_before"] = dependencies(packages)
        tooling = json.loads((PROJECT / "verification/tooling-lock.json").read_text())
        for rel, info in tooling["shared_tools"].items():
            if sha(REPOSITORY / rel) != info["sha256"]:
                raise RuntimeError(f"Shared tooling changed: {rel}")
        if args.infrastructure_only:
            sources = [pathlib.Path("KernelControl.lean")]
        else:
            sources = sorted(p.relative_to(PROJECT) for p in (PROJECT / "NLA").rglob("*.lean"))
            sources += sorted(p.relative_to(PROJECT) for p in PROJECT.glob("*.lean"))
            if not pathlib.Path("Challenge.lean") in sources:
                raise RuntimeError("Statement check requires Challenge.lean")
        retained = sources + [pathlib.Path(x) for x in ["lean-toolchain", "lakefile.toml",
                    "lake-manifest.json", "verification/check_local.py", "verification/tooling-lock.json"]]
        if args.compare_solution:
            retained.append(pathlib.Path("verification/check_comparator_core.py"))
        for optional in ["comparator.json", "verification/Inspect.lean"]:
            if (PROJECT / optional).is_file():
                retained.append(pathlib.Path(optional))
                if optional.endswith(".lean"):
                    sources.append(pathlib.Path(optional))
        for relative in dict.fromkeys(retained):
            src, dst = PROJECT / relative, snapshot / relative
            if src.is_symlink():
                raise RuntimeError(f"Refusing source symlink: {relative}")
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src, dst)
            copied_hash = sha(dst)
            if sha(src) != copied_hash:
                raise RuntimeError(f"Source changed while taking snapshot: {relative}")
            result["inputs"][str(relative)] = {"sha256": copied_hash, "bytes": dst.stat().st_size}
        runner = None
        if args.compare_solution:
            config_path = snapshot / "comparator.json"
            if not config_path.is_file():
                raise RuntimeError("--compare-solution requires comparator.json")
            config = json.loads(config_path.read_text())
            runner = comparator_runner(config)
            result["comparator_targets"] = config
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join([str(build)] + libs + [str(lean.parent.parent / "lib/lean")])
        env["PATH"] = str(lean.parent) + os.pathsep + env.get("PATH", "")
        result["lean_path"] = env["LEAN_PATH"]

        def run(relative, expected_success=True, rejection=None, execute=False):
            artifact = build / relative.with_suffix(".olean")
            artifact.parent.mkdir(parents=True, exist_ok=True)
            command = ([str(lean), "--run", str(relative)] if execute else
                       [str(lean), "-o", str(artifact), "-i", str(artifact.with_suffix(".ilean")), str(relative)])
            start = time.monotonic()
            cp = subprocess.run(command, cwd=snapshot, env=env, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=args.timeout)
            log = attempt / (str(relative).replace("/", "-") + ".log")
            log.write_text(cp.stdout)
            accepted = (cp.returncode == 0) if expected_success else (cp.returncode != 0 and rejection in cp.stdout)
            record = {"source": str(relative), "argv": command, "exit_code": cp.returncode,
                      "elapsed_seconds": time.monotonic() - start, "log": log.name,
                      "log_sha256": sha(log), "expected_success": expected_success,
                      "expectation_met": accepted}
            result["commands"].append(record)
            print(json.dumps(record), flush=True)
            if not accepted:
                raise RuntimeError(f"Lean check did not meet expectation: {relative}; see {log}")
            return cp.stdout

        for source in order_sources(sources, snapshot):
            run(source)
        # Audit every declaration owned by a concrete local module, including
        # auxiliary declarations that the author did not explicitly export.
        concrete = [p for p in sources if p.name != "Challenge.lean" and p.parts[0] != "verification"]
        for p in concrete:
            if re.search(r"^\s*(?:public\s+)?import\s+Challenge\b", (snapshot / p).read_text(), re.M):
                raise RuntimeError(f"Concrete module imports trusted Challenge: {p}")
        module_names = [str(p.with_suffix("")).replace(os.sep, ".") for p in concrete]
        audit_source = "import Lean\n" + "".join(f"import {name}\n" for name in module_names)
        audit_source += "\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n"
        audit_source += "  let localModules : Array Name := #[" + ", ".join("`" + n for n in module_names) + "]\n"
        audit_source += """  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[idx.toNat]? | continue
    if localModules.contains moduleName then
      let axioms ← liftCoreM <| collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "local declaration {name} uses prohibited axiom {axiomName}"
      checked := checked + 1
  logInfo m!"All {checked} concrete local declarations have permitted transitive axioms."
"""
        (snapshot / "AuditConcrete.lean").write_text(audit_source)
        result["generated_audit"] = {"sha256": sha(snapshot / "AuditConcrete.lean"), "modules": module_names}
        run(pathlib.Path("AuditConcrete.lean"))
        controls = {
            "RejectSorry.lean": ("theorem rejectSorry : True := by sorry\n#assert_trust kernel rejectSorry\n", "#assert_trust: 'rejectSorry' depends on sorry or unrecognized axioms"),
            "RejectNative.lean": ("theorem rejectNative : (1 : Nat) = 1 := by native_decide\n#assert_trust kernel rejectNative\n", "#assert_trust kernel: 'rejectNative' is not kernel-clean"),
        }
        for name, (body, expected_rejection) in controls.items():
            relative = pathlib.Path(name)
            (snapshot / relative).write_text("import Mathlib.Tactic\nimport LeanCert.Tactic.Verification\n" + body)
            result.setdefault("generated_controls", {})[name] = {"sha256": sha(snapshot / relative)}
            run(relative, expected_success=False, rejection=expected_rejection)
        if args.compare_solution:
            # Run the unmodified locked library only after all concrete source
            # declarations have passed the transitive axiom audit and controls.
            lock_path = REPOSITORY / "tools/lean/source-lock.json"
            lock_bytes = lock_path.read_bytes()
            lock_hash = hashlib.sha256(lock_bytes).hexdigest()
            snapshot_tooling = json.loads((snapshot / "verification/tooling-lock.json").read_text())
            if lock_hash != snapshot_tooling["shared_tools"]["tools/lean/source-lock.json"]["sha256"]:
                raise RuntimeError("Comparator source lock changed or differs from the snapshotted tooling lock")
            lock_copy = snapshot / "verification/comparator-source-lock.json"
            lock_copy.write_bytes(lock_bytes)
            lock = {entry["destination"]: entry for entry in json.loads(lock_bytes)["files"]}
            result["comparator_source_lock"] = {"sha256": lock_hash, "bytes": len(lock_bytes)}
            result["comparator_pinned_sources"] = {}
            for old, new in COMPARATOR_PINNED + [(".tools/comparator/LICENSE", "LICENSE-COMPARATOR")]:
                src, dst = COMPARATOR_ARCHIVE / old, snapshot / new
                info = lock[old]
                if src.is_symlink() or dst.exists():
                    raise RuntimeError(f"Refusing Comparator source symlink or snapshot collision: {old} -> {new}")
                if sha(src) != info["sha256"] or src.stat().st_size != info["bytes"]:
                    raise RuntimeError(f"Comparator source-lock mismatch: {src}")
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(src, dst)
                if sha(dst) != info["sha256"] or dst.stat().st_size != info["bytes"]:
                    raise RuntimeError(f"Comparator source changed while copying: {src}")
                result["comparator_pinned_sources"][new] = {
                    "source": str(src.relative_to(REPOSITORY)), "sha256": sha(dst), "bytes": dst.stat().st_size}
            for _, name in COMPARATOR_PINNED:
                run(pathlib.Path(name))
            runner_path = snapshot / "CompareSolution.lean"
            if runner_path.exists():
                raise RuntimeError("Refusing generated Comparator runner collision")
            runner_path.write_text(runner)
            result["generated_solution_comparator"] = {"sha256": sha(runner_path), "module_environments": "separate importModules calls"}
            final = run(pathlib.Path("CompareSolution.lean"), execute=True)
            if COMPARATOR_COMPLETION not in final:
                raise RuntimeError("Missing successful actual-theorem Comparator completion assertion")
            result["comparator_executed"] = True
            result["comparator_core_executed"] = True
            if sha(lock_path) != lock_hash:
                raise RuntimeError("Comparator source lock changed during verification")
            for info in result["comparator_pinned_sources"].values():
                if sha(REPOSITORY / info["source"]) != info["sha256"]:
                    raise RuntimeError("Comparator archive source changed during verification")
        _, result["dependencies_after"] = dependencies(packages)
        result["source_unchanged"] = all(sha(PROJECT / p) == info["sha256"] for p, info in result["inputs"].items())
        result["pass"] = result["source_unchanged"] and result["dependencies_before"] == result["dependencies_after"]
        if args.compare_solution and result["pass"] and result["comparator_core_executed"]:
            result["actual_targets_kernel_proof_checked"] = True
            result["ie06_targets_proved"] = True
            result["proof_scope"] = "Actual six Solution theorem proofs compiled and axiom-audited; exact Challenge types and referenced definitions compared by the locked local Comparator core. Trusted pinned dependency caches; no Linux sandbox, exporter, or raw kernel replay."
    except Exception as exc:
        result["error"] = str(exc)
    finally:
        result["removed_own_objects"] = {str(p.relative_to(build)): {"sha256": sha(p), "bytes": p.stat().st_size}
                                          for p in build.rglob("*") if p.is_file()}
        shutil.rmtree(build)
        result["own_output_directory_removed"] = not build.exists()
        receipt = attempt / "result.json"
        receipt.write_text(json.dumps(result, indent=2) + "\n")
        (evidence / "latest.json").write_text(json.dumps({"attempt": attempt.name,
                            "result_sha256": sha(receipt)}, indent=2) + "\n")
        print(json.dumps({"attempt": str(attempt), "pass": result["pass"], "error": result.get("error")}), flush=True)
    raise SystemExit(0 if result["pass"] else 1)


if __name__ == "__main__":
    main()
