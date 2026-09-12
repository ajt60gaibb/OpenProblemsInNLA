#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
command -v pdflatex >/dev/null || { echo 'pdflatex is required.' >&2; exit 1; }
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build src/report.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build src/report.tex
cp build/report.pdf RA04_partial_results.pdf
