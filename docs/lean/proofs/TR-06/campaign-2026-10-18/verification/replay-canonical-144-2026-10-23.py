#!/usr/bin/env python3
"""Rebuild the exact 144-source canonical TR06 proof checkpoint in fresh outputs.

The audit checks the literal intrinsic Target and all ten original export types; Linux Comparator remains separate.
Provide a Lean 4.33.1 compiler and the pinned Mathlib/LeanCert dependency cache.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--lean", type=Path, required=True)
parser.add_argument("--packages", type=Path, required=True)
parser.add_argument("--evidence-name", required=True,
                    help="A new, unused directory name beside the audit driver")
args = parser.parse_args()
directory = Path(__file__).resolve().parent
lock = json.loads((directory / "canonical-144-source-lock-2026-10-23.json").read_text())
records = lock["records"]
if len(records) != 144 or len({record["module"] for record in records}) != 144:
    raise RuntimeError("Expected the exact 144 distinct locked canonical Lean modules")
project = directory.parents[5] / "tensor-computations/TR-06/lean"
roots = [record["module"] for record in records if record["module"] != "Challenge"]
if len(roots) != 143:
    raise RuntimeError("Expected exactly 143 proof/definition roots plus separate Challenge")
command = [sys.executable, str(directory / "check-canonical-144-2026-10-23.py"),
           "--project", str(project), "--lean", str(args.lean.resolve()), "--packages", str(args.packages.resolve()),
           "--evidence-name", args.evidence_name, "--target-theorem", "NLA.TR06.target", "--root-module",
           *roots, "--build-only-module", "Challenge"]
raise SystemExit(subprocess.call(command, cwd=directory.parents[5]))
