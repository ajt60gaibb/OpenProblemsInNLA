#!/usr/bin/env python3
"""Render archived, reviewed native TeX manuscripts from a JSON manifest.

Usage: python tools/render_manuscripts.py references/.../manuscripts.json
XeLaTeX is required; set XELATEX if it is not on PATH. Exports are standalone.
"""
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]

def render(item, folder):
    def resolve(name):
        path = (folder / item[name]).resolve()
        path.relative_to(ROOT)
        return path
    source = resolve('source').read_text(encoding='utf-8')
    digest = hashlib.sha256(source.encode('utf-8')).hexdigest()
    review = resolve('review').read_text(encoding='utf-8')
    if digest not in review or 'PASS' not in review:
        raise ValueError('Source identity must match an independent PASS review')
    preamble = resolve('preamble').read_text(encoding='utf-8')
    tex = source.replace(r'\input{common_preamble}', preamble)
    if 'margin_mm' in item:
        margin = int(item['margin_mm'])
        if not 20 <= margin <= 35:
            raise ValueError('Manuscript margin must be between 20 and 35 mm')
        tex = tex.replace(r'\begin{document}', '\\geometry{margin=' + str(margin) + 'mm}\n\\begin{document}', 1)
    author = item['author']
    byline = author + r'\\\small Department of Applied Mathematics and Theoretical Physics' + r'\\\small University of Cambridge, Cambridge, United Kingdom' + r'\\\small\href{mailto:m.colbrook@damtp.cam.ac.uk}{m.colbrook@damtp.cam.ac.uk}'
    tex = tex.replace(r'\author{}', '\\author{' + byline + '}').replace(r'\date{}', r'\date{11 September 2026}')
    tex = tex.replace('pdfauthor={}', 'pdfauthor={' + author + '}')
    tex = tex.replace(r'\begin{document}', '\\usepackage{xurl}\n\\setlength{\\emergencystretch}{3em}\n\\begin{document}', 1)
    url = item['review_base_url'].rstrip('/') + '/' + resolve('review').relative_to(ROOT).as_posix()
    notice = '\n\\noindent\\textbf{' + item['status'] + '} ' + item['notice'] + '\nIndependent agent verification is not external human peer review or formal certification. Original draft remarks about review or source access reflect the input date; the dated \\href{' + url + '}{independent review} records the subsequent checks.\n\\par\\medskip\n'
    tex = tex.replace('\\maketitle\n', '\\maketitle\n' + notice + '% BEGIN REVIEWED BODY\n', 1)
    tex += '\n% END REVIEWED BODY\n'
    tex = '% Reviewed source SHA256 (UTF-8/LF): ' + digest + '\n' + tex
    output = resolve('output')
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='nla-manuscript-') as name:
        work = Path(name)
        (work/'manuscript.tex').write_text(tex,encoding='utf-8')
        for _ in range(2):
            run = subprocess.run([os.environ.get('XELATEX','xelatex'),'-interaction=nonstopmode','-halt-on-error','manuscript.tex'],cwd=work,capture_output=True,text=True,encoding='utf-8',errors='replace')
            if run.returncode:
                raise RuntimeError(output.name + ': ' + run.stdout[-4000:])
        log = (work/'manuscript.log').read_text(encoding='utf-8',errors='replace')
        warnings = re.findall(r'(?:Overfull[^\n]+|Missing character[^\n]+|[^\n]*undefined[^\n]*)',log)
        output.with_suffix('.tex').write_text(tex,encoding='utf-8')
        shutil.copyfile(work/'manuscript.pdf',output.with_suffix('.pdf'))
    return output.name, warnings

if __name__ == '__main__':
    manifest = Path(sys.argv[1]).resolve()
    items = json.loads(manifest.read_text(encoding='utf-8'))
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        for name,warnings in pool.map(lambda item: render(item,manifest.parent),items):
            print(name + ': ' + ('; '.join(warnings) if warnings else 'OK'),flush=True)
