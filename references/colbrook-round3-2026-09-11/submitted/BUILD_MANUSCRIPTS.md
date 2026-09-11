# Rebuilding the manuscripts

The supplied `.tex` files are standalone and contain no absolute local input paths. With a standard XeLaTeX installation, run twice on each file from a separate build directory:

```bash
xelatex -interaction=nonstopmode -halt-on-error ../manuscripts/IE-10-proposed-resolution.tex
xelatex -interaction=nonstopmode -halt-on-error ../manuscripts/IE-10-proposed-resolution.tex
xelatex -interaction=nonstopmode -halt-on-error ../manuscripts/IS-04-explicit-odd-family-partial.tex
xelatex -interaction=nonstopmode -halt-on-error ../manuscripts/IS-04-explicit-odd-family-partial.tex
```

The Markdown sources are included for editing or pasting. The supplied PDFs were compiled with XeLaTeX and visually inspected after rendering with Poppler. Do not overwrite the repository's canonical `problem.pdf` files with these separate proof manuscripts.

No font files are included. The LaTeX sources use the standard mathematical packages of a conventional TeX installation.
