#!/usr/bin/env sh
# Build the research note. Requires pdflatex and standard TeX Live packages.
set -eu
cd "$(dirname "$0")"
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT HUP INT TERM
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$build_dir" solution.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$build_dir" solution.tex
cp "$build_dir/solution.pdf" solution.pdf
