#!/usr/bin/env bash
# Run finite checks and, if pdfLaTeX is available, rebuild the report.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT"
export OPENBLAS_NUM_THREADS="${OPENBLAS_NUM_THREADS:-1}"
export OMP_NUM_THREADS="${OMP_NUM_THREADS:-1}"
python tests/exact_checks.py --output results/exact_checks.json 2>&1 | tee results/exact_execution.log
python tests/numerical_checks.py --output-dir results 2>&1 | tee results/numerical_execution.log
if command -v pdflatex >/dev/null 2>&1; then
  ./build.sh
else
  printf 'Finite checks finished; PDF rebuild skipped because pdflatex is not installed.\n'
fi
