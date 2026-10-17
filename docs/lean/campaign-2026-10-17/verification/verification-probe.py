#!/usr/bin/env python3
"""Reproduce a local, non-authoritative Lean/LeanCert runtime probe."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"],
            cwd=Path(__file__).resolve().parent, text=True).strip())
EVIDENCE = Path(__file__).with_name("verification-evidence")
LEAN = Path("/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin/lean")
PACKAGES = Path("/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages")


def capture(argv, **kwargs):
    proc = subprocess.run(argv, text=True, capture_output=True, **kwargs)
    return {"argv": list(map(str, argv)), "exit_code": proc.returncode,
            "stdout": proc.stdout, "stderr": proc.stderr}


def dependencies(manifest):
    results = []
    for package in manifest["packages"]:
        directory = PACKAGES / package["name"]
        head = capture(["git", "-C", str(directory), "rev-parse", "HEAD"])
        status = capture(["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"])
        ok = (head["exit_code"] == status["exit_code"] == 0
              and head["stdout"].strip() == package["rev"] and not status["stdout"].strip())
        results.append({"name": package["name"], "expected": package["rev"],
                        "directory": str(directory), "head": head, "status": status, "ok": ok})
    if not all(item["ok"] for item in results):
        raise RuntimeError("Dependency pins or tracked-source cleanliness failed")
    return results


EVIDENCE.mkdir(exist_ok=True)
manifest_source = capture(["git", "show", "origin/main:lean-statements/lake-manifest.json"], cwd=ROOT)
assert manifest_source["exit_code"] == 0
manifest = json.loads(manifest_source["stdout"])
result = {"scope": "Local macOS runtime probe only; no NLA target proof or authoritative Linux Comparator run",
          "baseline": capture(["git", "rev-parse", "origin/main"], cwd=ROOT),
          "platform": capture(["uname", "-a"]), "lean_version": capture([str(LEAN), "--version"]),
          "lean_binary_sha256": hashlib.sha256(LEAN.read_bytes()).hexdigest(),
          "dependencies_before": dependencies(manifest), "commands": []}
sources = {
    "KernelPositive": '''import Mathlib.Tactic
import LeanCert.Tactic.Verification
set_option leancert.trust "kernel"
theorem probe : (2 : ℚ) / 3 + 1 / 3 = 1 := by
  norm_num
#assert_trust kernel probe
#print axioms probe
''',
    "RejectSorry": '''import Mathlib.Tactic
import LeanCert.Tactic.Verification
theorem probe : True := by sorry
#print axioms probe
#assert_trust kernel probe
''',
    "RejectNative": '''import Mathlib.Tactic
import LeanCert.Tactic.Verification
theorem probe : (List.range 37).reverse.length = 37 := by native_decide
#print axioms probe
#assert_trust kernel probe
''',
}
with tempfile.TemporaryDirectory(prefix="nla-oct17-verification-probe-") as temporary:
    out = Path(temporary)
    env = os.environ.copy()
    env["LEAN_PATH"] = ":".join([str(out)] + [str(PACKAGES / item["name"] / ".lake/build/lib/lean")
        for item in manifest["packages"] if (PACKAGES / item["name"] / ".lake/build/lib/lean").is_dir()]
        + [str(LEAN.parent.parent / "lib/lean")])
    for name, source in sources.items():
        source_path = EVIDENCE / (name + ".lean.txt")
        source_path.write_text(source)
        working_source = out / (name + ".lean")
        working_source.write_text(source)
        record = capture([str(LEAN), "-R", str(out), "-o", str(out / (name + ".olean")), str(working_source)],
                         cwd=out, env=env, timeout=90)
        record["source_sha256"] = hashlib.sha256(source.encode()).hexdigest()
        record["name"] = name
        (EVIDENCE / (name + ".log")).write_text(record["stdout"] + record["stderr"])
        result["commands"].append(record)
    numerical_source = '''import LeanCert.Tactic.LeanCert
import LeanCert.Tactic.Verification
set_option leancert.trust "kernel"
theorem numericProbe : Real.log 2 < (7 : ℝ) / 10 := by
  leancert (trust := kernel)
#assert_trust kernel numericProbe
#print axioms numericProbe
'''
    (EVIDENCE / "NumericalAvailability.lean.txt").write_text(numerical_source)
    numerical_path = out / "NumericalAvailability.lean"
    numerical_path.write_text(numerical_source)
    numerical = capture([str(LEAN), "-R", str(out), str(numerical_path)], cwd=out, env=env, timeout=90)
    result["numerical_tactic_availability"] = numerical
    (EVIDENCE / "NumericalAvailability.log").write_text(numerical["stdout"] + numerical["stderr"])
result["dependencies_after"] = dependencies(manifest)
positive, sorry, native = result["commands"]
result["passed"] = (positive["exit_code"] == 0 and sorry["exit_code"] != 0
                    and "sorryAx" in sorry["stdout"]
                    and native["exit_code"] != 0 and "native_decide.ax" in native["stdout"])
(EVIDENCE / "result.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": result["passed"], "evidence": str(EVIDENCE),
                  "results": [{"name": item["name"], "exit_code": item["exit_code"]}
                              for item in result["commands"]]}, indent=2))
raise SystemExit(0 if result["passed"] else 1)
