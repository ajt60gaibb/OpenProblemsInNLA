#!/bin/sh
# Rebuild local outputs without overwriting the supplied manuscript or reports.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
mkdir -p build
python3 verification/verify.py --output build/results.json
command -v pdflatex >/dev/null 2>&1 || {
  echo 'pdflatex is required to rebuild the PDF; exact checks have completed.' >&2
  exit 1
}
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build PF04_proposed_proof.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build PF04_proposed_proof.tex
printf '\nRebuilt PDF: build/PF04_proposed_proof.pdf\nExact checks: build/results.json\n'
