#!/usr/bin/env python3
"""Build the MF-06 standalone LaTeX source, optionally its PDF.

Requires Pandoc for source conversion. With --pdf, requires XeLaTeX and runs
two passes.
Example: python3 build_solution.py --markdown solution.md --tex solution.tex
"""
from argparse import ArgumentParser
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile

PREAMBLE = r"""% Generated from the accompanying solution.md by build_solution.py.
% Standalone build: xelatex solution.tex (run twice).
\documentclass[11pt,a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage{lmodern,amsmath,amssymb,mathtools,microtype}
\usepackage[margin=27mm,headheight=14pt]{geometry}
\usepackage{booktabs,xurl,hyperref,fancyhdr,needspace}
\hypersetup{hidelinks,pdftitle={MF-06: A pointwise Lipschitz lower bound for the joint spectral radius},pdfauthor={George Stepaniants}}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small MF-06 / Joint spectral radius}
\fancyfoot[C]{\thepage}
\setlength{\parindent}{0pt}
\setlength{\parskip}{4pt}
\setlength{\emergencystretch}{2em}
\setcounter{secnumdepth}{0}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\title{\textbf{MF-06: A pointwise Lipschitz lower bound\\for the joint spectral radius}}
\author{George Stepaniants\\[3pt]\small Department of Computing and Mathematical Sciences\\\small California Institute of Technology\\\small Pasadena, California, USA}
\date{12 September 2026}
\begin{document}
\maketitle
"""


def improve_layout(fragment):
    """Pure typography: preserve the Markdown and every mathematical token."""
    fragment = fragment.replace("§", r"\S{}")
    for paragraph, lines in [
        ("Choose a fixed complement and write the generators as", 6),
        ("Consider two distinct degree-", 9),
    ]:
        assert fragment.count(paragraph) == 1
        fragment = fragment.replace(paragraph, rf"\Needspace{{{lines}\baselineskip}}" + "\n" + paragraph)
    fragment = re.sub(r"\b(Lemma|Section|Theorem|Proposition|Definition) ([0-9]+)",
                      r"\1~\2", fragment)
    fragment = fragment.replace(r"family \(i\).", r"family~\(i\).")
    fragment = fragment.replace(r" \(\square\)", r"\unskip\nobreak\hfill\(\square\)")
    return fragment


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--markdown", type=Path, default=Path("solution.md"))
    parser.add_argument("--tex", type=Path, default=Path("solution.tex"))
    parser.add_argument("--pandoc", default=os.environ.get("PANDOC", "pandoc"))
    parser.add_argument("--xelatex", default=os.environ.get("XELATEX", "xelatex"))
    parser.add_argument("--pdf", action="store_true")
    args = parser.parse_args()
    text = args.markdown.read_text()
    title, byline, body = text.split("\n\n", 2)
    assert title == "# MF-06: A pointwise Lipschitz lower bound for the joint spectral radius"
    assert byline == ("**George Stepaniants**  \n"
                      "Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA  \n"
                      "12 September 2026")
    conversion = subprocess.run(
        [args.pandoc, "--from=markdown+tex_math_dollars+raw_tex", "--to=latex",
         "--shift-heading-level-by=-1", "--wrap=none"],
        input=body, text=True, capture_output=True, check=True,
    )
    args.tex.write_text(PREAMBLE + improve_layout(conversion.stdout) + "\n\\end{document}\n")
    print(f"Wrote standalone LaTeX source: {args.tex}")
    if not args.pdf:
        return
    tex = args.tex.resolve()
    with tempfile.TemporaryDirectory(prefix="mf06-xelatex-") as scratch:
        for number in [1, 2]:
            completed = subprocess.run(
                [args.xelatex, "-interaction=nonstopmode", "-halt-on-error",
                 "-file-line-error", f"-output-directory={scratch}", str(tex)],
                cwd=tex.parent, text=True, capture_output=True,
            )
            (tex.parent / f"solution-xelatex-pass-{number}.log").write_text(completed.stdout + completed.stderr)
            completed.check_returncode()
        shutil.copy2(Path(scratch) / (tex.stem + ".pdf"), tex.with_suffix(".pdf"))
        shutil.copy2(Path(scratch) / (tex.stem + ".log"), tex.parent / "solution-xelatex.log")
    print(f"Wrote PDF: {tex.with_suffix('.pdf')}")


if __name__ == "__main__":
    main()
