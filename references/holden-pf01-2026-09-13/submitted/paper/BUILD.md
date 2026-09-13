# Build the mathematical manuscript

The PDF was built with pdfLaTeX. From this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error pf01_structural_obstructions.tex
pdflatex -interaction=nonstopmode -halt-on-error pf01_structural_obstructions.tex
```

The packages used are standard TeX packages: amsmath, amssymb, amsthm, mathtools, geometry, lmodern, microtype, hyperref, xurl, booktabs, array, longtable, and enumitem. Only the source and final PDF are included; auxiliary build files are omitted.
