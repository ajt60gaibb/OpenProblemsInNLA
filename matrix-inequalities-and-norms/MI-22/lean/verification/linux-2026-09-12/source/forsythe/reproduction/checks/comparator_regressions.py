#!/usr/bin/env python3
"""Replay the four retained official fixtures and one exact type mismatch.

Run after preparing .tools. Output goes to stdout for the caller to retain.
Every case uses the Comparator sandbox with the systemd AF_UNIX restriction.
"""

import json
from pathlib import Path
import shutil
import subprocess
import tempfile


LEAN_ROOT = Path(__file__).resolve().parents[2]
CASES = [
    ("simple_match", 0, "Your solution is okay!"),
    ("simple_mismatch", 1, "Challenge and solution constant kind don't match: 'comm'"),
    ("simple_axiom_issue", 1, "Illegal axiom detected: 'helper'"),
    # This official fixture also exercises the axiom check despite its name.
    ("simple_kind_mismatch", 1, "Illegal axiom detected: 'helper'"),
    ("type_mismatch", 1, "Challenge and solution theorem statement do not match: 'checked'"),
]
LAKEFILE = '''name = "ComparatorRegression"
[[lean_lib]]
name = "Challenge"
[[lean_lib]]
name = "Solution"
'''


def main() -> int:
    temporary_root = LEAN_ROOT / ".verification-tmp"
    temporary_root.mkdir(exist_ok=True)
    fixtures = LEAN_ROOT / ".tools/comparator/tests/projects"
    print("Comparator regressions: RestrictAddressFamilies=~AF_UNIX; .tools/env.sh selects the real strict sandbox.", flush=True)
    passed = True
    with tempfile.TemporaryDirectory(prefix="comparator regressions ", dir=temporary_root) as temporary:
        for name, expected_exit, marker in CASES:
            project = Path(temporary) / name
            if name == "type_mismatch":
                project.mkdir()
                (project / "Challenge.lean").write_text("theorem checked : (1 : Nat) = 1 := by rfl\n")
                (project / "Solution.lean").write_text("theorem checked : (2 : Nat) = 2 := by rfl\n")
                (project / "config.json").write_text(json.dumps({
                    "challenge_module": "Challenge", "solution_module": "Solution",
                    "theorem_names": ["checked"],
                    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
                }, indent=2) + "\n")
            else:
                shutil.copytree(fixtures / name, project)
            if not (project / "lakefile.toml").exists():
                (project / "lakefile.toml").write_text(LAKEFILE)
            shutil.copyfile(LEAN_ROOT / "lean-toolchain", project / "lean-toolchain")
            command = [
                "systemd-run", "--user", "--quiet", "--wait", "--pipe",
                "-p", "RestrictAddressFamilies=~AF_UNIX",
                "/bin/bash", "--noprofile", "--norc", "-c",
                'set -euo pipefail\nsource "$1"\ncd -- "$2"\nexec lake env "$COMPARATOR_BIN" config.json',
                "comparator-regression", str(LEAN_ROOT / ".tools/env.sh"), str(project),
            ]
            print(f"\nCASE {name}", flush=True)
            result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            print(result.stdout, end="", flush=True)
            required = ["Building Challenge", "Building Solution", "from Challenge", "from Solution", marker]
            if expected_exit == 0:
                required.append("Lean default kernel accepts the solution")
            missing = [text for text in required if text not in result.stdout]
            accepted = result.returncode == expected_exit and not missing
            passed = passed and accepted
            print(f"{'PASS' if accepted else 'FAIL'} {name}: exit {result.returncode}, expected {expected_exit}; required phase: {marker}", flush=True)
            if missing:
                print(f"Missing output markers: {missing}", flush=True)
    print("PASS: all five Comparator regressions" if passed else "FAIL: Comparator regressions", flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
