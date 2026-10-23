#!/usr/bin/env python3
"""Rebuild the exact 80-module complete TR06 proof checkpoint in fresh outputs.

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
lock = json.loads((directory / "full-target-80-source-lock-2026-10-23.json").read_text())
records = lock["records"]
if len(records) != 80 or len({record["module"] for record in records}) != 80:
    raise RuntimeError("Expected the exact 80 distinct locked proof modules")
command = [sys.executable, str(directory / "check-full-target-80-2026-10-23.py"),
           "--lean", str(args.lean.resolve()), "--packages", str(args.packages.resolve()),
           "--evidence-name", args.evidence_name, "--target-theorem", "NLA.Proofs.TR06.target", "--root-module",
           *[record["module"] for record in records]]
raise SystemExit(subprocess.call(command, cwd=directory.parents[5]))
