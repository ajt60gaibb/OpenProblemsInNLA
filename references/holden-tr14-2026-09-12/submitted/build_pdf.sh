#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
OUT="${1:-$ROOT/build}"
command -v pdflatex >/dev/null 2>&1 || { printf 'pdflatex is required.\n' >&2; exit 1; }
mkdir -p "$OUT"
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$OUT" "$ROOT/source/TR14_solution.tex"
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$OUT" "$ROOT/source/TR14_solution.tex"
printf '\nRebuilt PDF: %s/TR14_solution.pdf\n' "$OUT"
