#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
  echo 'pdflatex is required; install LaTeX and the packages named in the source.' >&2
  exit 1
fi
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cp "$ROOT"/manuscript/*.tex "$WORK/"
cd "$WORK"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error re03_extended_results.tex
done
cp re03_extended_results.pdf "$ROOT/manuscript/re03_extended_results.pdf"
printf '%s\n' 'PDF rebuilt. Its original checksum may no longer match SHA256SUMS.txt.'
