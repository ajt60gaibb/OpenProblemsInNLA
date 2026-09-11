#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
./build.sh
mkdir -p rerun
python3 tests/check_data.py | tee rerun/data_tests.log
# Membership (the witness checks above) and inclusion (the checks below)
# are BOTH required for a range certificate.
python3 - <<'PY'
import json, subprocess
from pathlib import Path
root=Path.cwd(); claims=json.loads((root/'claims.json').read_text())
with (root/'rerun/full_matrix_checks.log').open('w') as log:
    for n in claims['ac11_verified_orders']:
        args=[str(root/'build/verify_permanent'),str(root/f'data/ac11/min{n}.txt'),'1']
        result=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        print(result.stdout,end='');log.write(result.stdout);log.flush()
        if result.returncode:raise SystemExit(result.returncode)
with (root/'rerun/range_checks.log').open('w') as log:
    for n in claims['ac12_verified_orders']:
        args=[str(root/'build/check_range'),str(n),str(root/f'data/ac12/u{n}_spectrum.txt'),str(root/f'rerun/range{n}')]
        result=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        print(result.stdout,end='');log.write(result.stdout);log.flush()
        if result.returncode:raise SystemExit(result.returncode)
PY
