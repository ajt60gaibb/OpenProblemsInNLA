#!/usr/bin/env python3
"""Rebuild the exact 70-module recovered TR06 support checkpoint in fresh outputs.

The audit does not prove the final intrinsic Target or run Linux Comparator.
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
lock = json.loads((directory / "recovered-support-70-source-lock-2026-10-23.json").read_text())
records = lock["records"]
if len(records) != 70 or len({record["module"] for record in records}) != 70:
    raise RuntimeError("Expected the exact 70 distinct locked support modules")
command = [sys.executable, str(directory / "check-recovered-support-2026-10-23.py"),
           "--lean", str(args.lean.resolve()), "--packages", str(args.packages.resolve()),
           "--evidence-name", args.evidence_name, "--root-module",
           *[record["module"] for record in records]]
raise SystemExit(subprocess.call(command, cwd=directory.parents[5]))
