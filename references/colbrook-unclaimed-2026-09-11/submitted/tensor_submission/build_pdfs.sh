#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
mkdir -p pdf
cd tex
for id in TR06 TR15 TR17 TR19 TR20 TR04; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory ../pdf "$id.tex"
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory ../pdf "$id.tex"
done
