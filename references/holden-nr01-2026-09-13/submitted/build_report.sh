#!/bin/sh
set -eu
cd "$(dirname "$0")/report"
pdflatex -interaction=nonstopmode -halt-on-error NR01_round2.tex
pdflatex -interaction=nonstopmode -halt-on-error NR01_round2.tex
