#!/usr/bin/env python3
"""Add submission front matter to independently reviewed standalone TeX.

Usage: python tools/render_reviewed_tex.py references/.../manuscripts.json
Requires XeLaTeX; XELATEX can specify its executable.
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
    def resolve(key):
        path = (folder / item[key]).resolve()
        path.relative_to(ROOT)
        return path

    source = resolve('source').read_text(encoding='utf-8')
    digest = hashlib.sha256(source.encode('utf-8')).hexdigest()
    review = resolve('review').read_text(encoding='utf-8')
    if digest not in review or 'PASS' not in review:
        raise ValueError('Complete source identity must match a PASS review')
    author = item['author']
    byline = author + r'\\\small Department of Applied Mathematics and Theoretical Physics'
    byline += r'\\\small University of Cambridge, Cambridge, United Kingdom'
    byline += r'\\\small\href{mailto:m.colbrook@damtp.cam.ac.uk}{m.colbrook@damtp.cam.ac.uk}'
    tex = source.replace(r'\author{}', '\\author{' + byline + '}', 1)
    tex = tex.replace(r'\date{}', r'\date{11 September 2026}', 1)
    layout = '\\usepackage{xurl}\n\\setlength{\\emergencystretch}{3em}\n'
    layout += '\\hypersetup{pdfauthor={' + author + '}}\n'
    if item.get('bibliography_new_page'):
        layout += r'\let\originalthebibliography\thebibliography' + '\n'
        layout += r'\renewcommand{\thebibliography}[1]{\clearpage\originalthebibliography{#1}}' + '\n'
    if 'margin_mm' in item:
        margin = int(item['margin_mm'])
        if not 20 <= margin <= 35:
            raise ValueError('Margin must be between 20 and 35 mm')
        layout += '\\geometry{margin=' + str(margin) + 'mm}\n'
    tex = tex.replace(r'\begin{document}', layout + r'\begin{document}', 1)
    url = item['review_base_url'].rstrip('/') + '/' + resolve('review').relative_to(ROOT).as_posix()
    notice = '\n\\noindent\\textbf{' + item['status'] + '} ' + item['notice']
    notice += '\nThe dated \\href{' + url + '}{independent agent review} records the subsequent checks and supersedes original draft remarks about pending review. This is not external human peer review or formal certification.\n\\par\\medskip\n'
    tex = tex.replace(r'\maketitle', '\\maketitle\n' + notice + '% BEGIN REVIEWED BODY\n', 1)
    tex += '\n% END REVIEWED BODY\n'
    tex = '% Reviewed source SHA256 (UTF-8/LF): ' + digest + '\n' + tex
    output = resolve('output')
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='nla-reviewed-tex-') as name:
        work = Path(name)
        (work / 'manuscript.tex').write_text(tex, encoding='utf-8')
        for _ in range(2):
            run = subprocess.run([os.environ.get('XELATEX', 'xelatex'), '-interaction=nonstopmode', '-halt-on-error', 'manuscript.tex'], cwd=work, capture_output=True, text=True, encoding='utf-8', errors='replace')
            if run.returncode:
                raise RuntimeError(output.name + ': ' + run.stdout[-4000:])
        log = (work / 'manuscript.log').read_text(encoding='utf-8', errors='replace')
        warnings = re.findall(r'(?:Overfull[^\n]+|Missing character[^\n]+|[^\n]*undefined[^\n]*)', log)
        output.with_suffix('.tex').write_text(tex, encoding='utf-8')
        shutil.copyfile(work / 'manuscript.pdf', output.with_suffix('.pdf'))
    return output.name, warnings


if __name__ == '__main__':
    manifest = Path(sys.argv[1]).resolve()
    items = json.loads(manifest.read_text(encoding='utf-8'))
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        for name, warnings in pool.map(lambda item: render(item, manifest.parent), items):
            print(name + ': ' + ('; '.join(warnings) if warnings else 'OK'), flush=True)
