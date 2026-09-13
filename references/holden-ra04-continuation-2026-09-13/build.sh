#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build src/report.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build src/report.tex
cp build/report.pdf report.pdf
