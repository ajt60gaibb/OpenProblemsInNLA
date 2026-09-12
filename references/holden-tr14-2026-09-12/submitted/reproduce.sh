#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
PYTHON="${PYTHON:-python3}"
OUT="${1:-$ROOT/reproduced_checks}"
mkdir -p "$OUT"
"$PYTHON" "$ROOT/code/verify_solution.py" --suite all --output "$OUT/verification.json"
"$PYTHON" "$ROOT/code/verify_certificates.py" --output "$OUT/certificates.json"
"$PYTHON" "$ROOT/code/hankel_rank.py" -m 5 -n 3 \
  --moments-file "$ROOT/examples/mixed_double_and_two_simple_moments.json" \
  --output "$OUT/mixed_rank.json"
"$PYTHON" "$ROOT/code/binary_certificate.py" -m 5 -n 3 \
  --moments-file "$ROOT/examples/two_double_points_moments.json" \
  --verify-full-tensor --output "$OUT/two_double_points_certificate.json"
printf '\nAll checks passed. Outputs: %s\n' "$OUT"
