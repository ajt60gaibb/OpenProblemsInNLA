#!/usr/bin/env python3
"""Render independently reviewed TeX proofs referenced by solution.md metadata.

Called by render_solutions.py when a manuscript supplies proof-source metadata.
The reviewed proof is embedded unchanged; bibliography data is embedded after
BibTeX so the exported solution.tex is independently compilable with XeLaTeX.
"""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]

def render(source):
    identifier = source.parent.name
    front = source.read_text(encoding='utf-8').split('---', 2)[1]
    fields = {key: json.loads(value) for key, value in re.findall(r'^([a-z-]+): (".*")$', front, re.M)}
    def resolve(key):
        path = (source.parent / fields[key]).resolve()
        path.relative_to(ROOT)
        return path
    proof = resolve('proof-source').read_text(encoding='utf-8')
    preamble = resolve('preamble-source').read_text(encoding='utf-8')
    bibliography = resolve('bibliography-source').read_text(encoding='utf-8')
    preamble = preamble.replace(r'\documentclass[11pt]{article}', r'\documentclass[10pt,a4paper]{article}')
    preamble = preamble.replace(r'\usepackage[margin=1in]{geometry}', r'\usepackage[margin=24mm]{geometry}')
    preamble = preamble.replace('pdfauthor={AI-assisted draft prepared for the requester}', 'pdfauthor={Matthew J. Colbrook}')
    preamble = preamble.replace('OpenProblemsInNLA: proposed resolutions', fields['document-kind'] + ' / ' + identifier)
    preamble += '\n\\usepackage{xurl}\n\\setlength{\\emergencystretch}{3em}\n\\allowdisplaybreaks[1]\n'
    # A compact title keeps the final proof lines and references together.
    if identifier in {'MI-09', 'MI-22'}:
        preamble += r'''
\makeatletter
\renewcommand{\@maketitle}{\newpage\null\begin{center}
{\Large\@title\par}\vskip .8em
{\normalsize\begin{tabular}[t]{c}\@author\end{tabular}\par}\vskip .5em
{\small\@date}\end{center}\par\vskip .5em}
\makeatother
'''
    review_path = resolve('review-source').relative_to(ROOT).as_posix()
    review_url = 'https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/' + review_path
    status = fields['catalog-status']
    prefix = preamble + rf'''
\title{{{identifier}: {fields['document-kind'].title()}}}
\author{{Matthew J. Colbrook\\
\small Department of Applied Mathematics and Theoretical Physics\\
\small University of Cambridge, Cambridge, United Kingdom\\
\small\href{{mailto:m.colbrook@damtp.cam.ac.uk}}{{m.colbrook@damtp.cam.ac.uk}}}}
\date{{11 September 2026}}
\begin{{document}}
\maketitle
\textbf{{Repository status: {status}.}}
The complete argument received an independent Codex-agent PASS review
{'for the stated partial result only' if status == 'Partially resolved' else 'against the exact catalog target'}.
The original draft was AI-assisted; the reviewed proof below is unchanged.
This is independent agent verification, not external human peer review or
formal proof certification. \href{{{review_url}}}{{Detailed review and scope}}.
\par\medskip
% BEGIN REVIEWED PROOF
'''
    suffix = '\n% END REVIEWED PROOF\n\\bibliographystyle{plainurl}\n\\bibliography{references}\n\\end{document}\n'
    tex = prefix + proof + suffix
    with tempfile.TemporaryDirectory(prefix=f'nla-latex-{identifier}-') as folder:
        work = Path(folder)
        (work / 'solution.tex').write_text(tex, encoding='utf-8')
        (work / 'references.bib').write_text(bibliography, encoding='utf-8')
        def run(command):
            result = subprocess.run(command, cwd=work, capture_output=True, text=True, encoding='utf-8', errors='replace')
            if result.returncode:
                raise RuntimeError(f'{identifier}: command failed\n{result.stdout[-4500:]}\n{result.stderr[-1000:]}')
        latex = [os.environ.get('XELATEX', 'xelatex'), '-interaction=nonstopmode', '-halt-on-error', 'solution.tex']
        run(latex)
        run([os.environ.get('BIBTEX', 'bibtex'), 'solution'])
        bbl = (work / 'solution.bbl').read_text(encoding='utf-8')
        tex = tex.replace('\\bibliographystyle{plainurl}\n\\bibliography{references}', bbl)
        (work / 'solution.tex').write_text(tex, encoding='utf-8')
        for _ in range(2):
            run(latex)
        log = (work / 'solution.log').read_text(encoding='utf-8', errors='replace')
        warnings = re.findall(r'(?:Overfull[^\n]+|Missing character[^\n]+|[^\n]*undefined[^\n]*)', log)
        (source.parent / 'solution.tex').write_text(tex, encoding='utf-8')
        shutil.copyfile(work / 'solution.pdf', source.parent / 'solution.pdf')
        return identifier, warnings
