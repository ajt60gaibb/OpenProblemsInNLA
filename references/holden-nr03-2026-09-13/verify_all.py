#!/usr/bin/env python3
"""Run the exact certificate check and supplementary tests using only Python."""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
for name in ("verify_certificate.py", "verify_minimal.py", "self_tests.py"):
    print(f"\n=== {name} ===", flush=True)
    subprocess.run([sys.executable, str(root / "code" / name)], check=True, cwd=root)
print("\nCOMPLETE: NR-03 is false; the exact witness has rank_+(C_7) <= 127 < 128.", flush=True)
print("127 is an upper bound, not a claim that the exact nonnegative rank equals 127.", flush=True)
