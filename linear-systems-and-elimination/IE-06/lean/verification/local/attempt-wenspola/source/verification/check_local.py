#!/usr/bin/env python3
"""Check a fresh source snapshot using pinned, read-only local dependency caches.

This development check is deliberately separate from tools/lean/verify.sh. It
does not provide Linux sandbox isolation, kernel replay, or Comparator proof
verification, and never converts Challenge's intentional holes into proofs.
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
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()
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
        "phase": "local infrastructure check" if args.infrastructure_only else "local statement elaboration",
        "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "platform": platform.platform(), "argv": list(__import__("sys").argv),
        "commands": [], "inputs": {}, "pass": False,
        "authoritative_linux_comparator": False, "comparator_executed": False,
        "ie06_targets_proved": False,
        "challenge_holes_are_reference_signatures_only": True,
        "cache_limit": "Tracked sources/pins checked; compiled dependency cache is trusted local development input.",
    }
    build = pathlib.Path(tempfile.mkdtemp(prefix="nla-ie06-local-"))
    try:
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
            result["inputs"][str(relative)] = {"sha256": sha(src), "bytes": src.stat().st_size}
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join([str(build)] + libs + [str(lean.parent.parent / "lib/lean")])
        env["PATH"] = str(lean.parent) + os.pathsep + env.get("PATH", "")
        result["lean_path"] = env["LEAN_PATH"]

        def run(relative, expected_success=True, rejection=None):
            artifact = build / relative.with_suffix(".olean")
            artifact.parent.mkdir(parents=True, exist_ok=True)
            command = [str(lean), "-o", str(artifact), "-i", str(artifact.with_suffix(".ilean")), str(relative)]
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

        for source in order_sources(sources, snapshot):
            run(source)
        controls = {
            "RejectSorry.lean": ("theorem rejectSorry : True := by sorry\n#assert_trust kernel rejectSorry\n", "#assert_trust: 'rejectSorry' depends on sorry or unrecognized axioms"),
            "RejectNative.lean": ("theorem rejectNative : (1 : Nat) = 1 := by native_decide\n#assert_trust kernel rejectNative\n", "#assert_trust kernel: 'rejectNative' is not kernel-clean"),
        }
        for name, (body, expected_rejection) in controls.items():
            relative = pathlib.Path(name)
            (snapshot / relative).write_text("import Mathlib.Tactic\nimport LeanCert.Tactic.Verification\n" + body)
            result.setdefault("generated_controls", {})[name] = {"sha256": sha(snapshot / relative)}
            run(relative, expected_success=False, rejection=expected_rejection)
        _, result["dependencies_after"] = dependencies(packages)
        result["source_unchanged"] = all(sha(PROJECT / p) == info["sha256"] for p, info in result["inputs"].items())
        result["pass"] = result["source_unchanged"] and result["dependencies_before"] == result["dependencies_after"]
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
