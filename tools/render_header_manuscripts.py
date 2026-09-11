#!/usr/bin/env python3
"""Render reviewed manuscripts that use a shared preamble and header command.

Usage: python tools/render_header_manuscripts.py references/.../manuscripts.json
Both complete source and preamble hashes must appear in the independent review.
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
    preamble = resolve('preamble').read_text(encoding='utf-8')
    review = resolve('review').read_text(encoding='utf-8')
    hashes = [hashlib.sha256(s.encode()).hexdigest() for s in (source, preamble)]
    if 'PASS' not in review or any(h not in review for h in hashes):
        raise ValueError('Full manuscript and preamble identities require a PASS review')
    lines = source.splitlines(keepends=True)
    headers = [i for i, line in enumerate(lines) if line.startswith(r'\header{')]
    if len(headers) != 1 or source.count(r'\input{common.tex}') != 1:
        raise ValueError('Expected one header and shared preamble input')
    i = headers[0]
    before, body = ''.join(lines[:i+1]), ''.join(lines[i+1:])
    layout = '\n\\usepackage{xurl}\n\\setlength{\\emergencystretch}{3em}\n'
    layout += '\\hypersetup{pdfauthor={Matthew J. Colbrook},pdftitle={' + item['title'] + '}}\n'
    if 'margin_mm' in item:
        margin = int(item['margin_mm'])
        if not 20 <= margin <= 35:
            raise ValueError('Margin out of range')
        layout += '\\geometry{margin=' + str(margin) + 'mm}\n'
    before = before.replace(r'\input{common.tex}', preamble + layout, 1)
    byline = r'\begin{center}Matthew J. Colbrook\\{\small Department of Applied Mathematics and Theoretical Physics\\University of Cambridge, Cambridge, United Kingdom\\\href{mailto:m.colbrook@damtp.cam.ac.uk}{m.colbrook@damtp.cam.ac.uk}}\\11 September 2026\end{center}'
    url = item['review_base_url'].rstrip('/') + '/' + resolve('review').relative_to(ROOT).as_posix()
    notice = '\n\\textbf{' + item['status'] + '} ' + item['notice']
    notice += '\nThe dated \\href{' + url + '}{independent agent review} supersedes the original pending-review header. Agent review is not external human peer review or formal certification. The source archive describes these as AI-generated drafts; authorship is attributed at the submitter\'s request.\n\\par\\medskip\n'
    tex = '% Full source/preamble SHA256 (UTF-8/LF): ' + ' '.join(hashes) + '\n'
    tex += before + byline + notice + '% BEGIN REVIEWED BODY\n' + body + '\n% END REVIEWED BODY\n'
    output = resolve('output')
    with tempfile.TemporaryDirectory(prefix='nla-header-manuscript-') as directory:
        work = Path(directory)
        (work/'manuscript.tex').write_text(tex, encoding='utf-8')
        for _ in range(2):
            result = subprocess.run([os.environ.get('XELATEX','xelatex'),'-interaction=nonstopmode','-halt-on-error','manuscript.tex'], cwd=work, capture_output=True, text=True, encoding='utf-8', errors='replace')
            if result.returncode:
                raise RuntimeError(output.name + ': ' + result.stdout[-4000:])
        log = (work/'manuscript.log').read_text(encoding='utf-8', errors='replace')
        warnings = re.findall(r'(?:Overfull[^\n]+|Missing character[^\n]+|[^\n]*undefined[^\n]*)', log)
        output.with_suffix('.tex').write_text(tex, encoding='utf-8')
        shutil.copyfile(work/'manuscript.pdf', output.with_suffix('.pdf'))
    return output.name, warnings


if __name__ == '__main__':
    manifest = Path(sys.argv[1]).resolve()
    items = json.loads(manifest.read_text(encoding='utf-8'))
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        for name, warnings in pool.map(lambda item: render(item, manifest.parent), items):
            print(name + ': ' + ('; '.join(warnings) if warnings else 'OK'), flush=True)
