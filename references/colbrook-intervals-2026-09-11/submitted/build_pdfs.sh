#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/manuscripts"
for name in overview AV-01 AV-02 IV-02_IV-04 IV-03 IV-05 IV-06; do
  pdflatex -interaction=nonstopmode -halt-on-error "$name.tex"
  pdflatex -interaction=nonstopmode -halt-on-error "$name.tex"
done
printf '\nIndividual PDFs rebuilt. The bundled reader is a concatenation in the order above.\n'
