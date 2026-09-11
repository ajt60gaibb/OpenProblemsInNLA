#!/bin/sh
# Build in a temporary directory so no LaTeX intermediates enter the package.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
command -v pdflatex >/dev/null 2>&1 || { echo "pdflatex is required" >&2; exit 2; }
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT HUP INT TERM
cp "$ROOT/manuscript/sharp_random_pivoting.tex" "$WORK/"
(
  cd "$WORK"
  pdflatex -interaction=nonstopmode -halt-on-error sharp_random_pivoting.tex
  pdflatex -interaction=nonstopmode -halt-on-error sharp_random_pivoting.tex
)
cp "$WORK/sharp_random_pivoting.pdf" "$ROOT/manuscript/sharp_random_pivoting.pdf"
printf '%s\n' "Built manuscript/sharp_random_pivoting.pdf"
