#!/bin/sh
# Rebuild solution.pdf without leaving intermediate files in the package.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "Error: pdflatex is required to rebuild the manuscript." >&2
    exit 1
fi
BUILD=$(mktemp -d "${TMPDIR:-/tmp}/ie16-pdf.XXXXXX")
trap 'rm -rf "$BUILD"' EXIT HUP INT TERM
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$BUILD" "$ROOT/source/solution.tex"
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$BUILD" "$ROOT/source/solution.tex"
cp "$BUILD/solution.pdf" "$ROOT/solution.pdf"
printf '\nBuilt %s\n' "$ROOT/solution.pdf"
