#!/usr/bin/env bash
# Rebuild the mathematical report. Requires pdfLaTeX and the packages listed in README.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
  printf 'pdflatex is required. Install a TeX distribution with the packages listed in README.md.\n' >&2
  exit 1
fi
mkdir -p "$ROOT/build"
export TEXINPUTS="$ROOT/src:${TEXINPUTS:-}"
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    -output-directory="$ROOT/build" "$ROOT/src/report.tex" \
    > "$ROOT/build/compile-pass-$pass.log"
done
if grep -Eq 'There were undefined references|There were undefined citations|Overfull \\[hv]box' "$ROOT/build/report.log"; then
  printf 'Build completed, but unresolved references or an overfull box need inspection.\n' >&2
  exit 1
fi
cp "$ROOT/build/report.pdf" "$ROOT/report.pdf"
printf 'Built %s\n' "$ROOT/report.pdf"
