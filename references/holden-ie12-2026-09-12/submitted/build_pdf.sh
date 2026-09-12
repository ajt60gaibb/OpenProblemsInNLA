#!/bin/sh
# Build without leaving LaTeX auxiliary files in the archive directory.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
BUILD=$(mktemp -d)
trap 'rm -rf "$BUILD"' EXIT HUP INT TERM
command -v pdflatex >/dev/null 2>&1 || {
  printf '%s\n' 'pdflatex is required. Install a LaTeX distribution with the source packages.' >&2
  exit 1
}
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$BUILD" \
  "$ROOT/paper/IE12_solution.tex"
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$BUILD" \
  "$ROOT/paper/IE12_solution.tex"
cp "$BUILD/IE12_solution.pdf" "$ROOT/IE12_solution.pdf"
printf '%s\n' "Built $ROOT/IE12_solution.pdf"
