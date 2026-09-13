#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1
export OMP_NUM_THREADS=1
export PYTHONDONTWRITEBYTECODE=1
python code/check_manifest.py
mkdir -p generated_results
python code/verify.py > generated_results/suite_stdout.json
python code/check_exact_certificate.py > generated_results/exact_full_rank_certificate_check.json
python code/check_freezing_certificate.py > generated_results/exact_fractional_freezing_check.json
python - <<'PY'
import json
from pathlib import Path
out = Path('generated_results')
r = json.loads((out/'verification.json').read_text())
assert r['passed'] and r['total_assertions'] == 7621
for name in ('exact_full_rank_certificate_check.json', 'exact_fractional_freezing_check.json'):
    assert json.loads((out/name).read_text())['passed']
print(f"PASS: {r['total_assertions']:,} finite suite assertions; both exact certificate checkers passed.")
print('New results are in generated_results/. Recorded results/ files are unchanged.')
print('These are finite checks, not independent review or proof-assistant verification.')
PY
