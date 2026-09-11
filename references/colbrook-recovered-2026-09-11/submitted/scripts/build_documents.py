#!/usr/bin/env python3
"""Build PDFs using pdflatex, and Markdown renditions using optional Pandoc."""
from __future__ import annotations
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import re,shutil,subprocess

ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'.build'

def compile_tex(path:Path)->None:
    for _ in range(2):
        run=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',
                            '-output-directory='+str(BUILD),str(path)],
                            cwd=ROOT,capture_output=True,text=True,timeout=90)
        if run.returncode:
            raise RuntimeError(f'LaTeX failed for {path.name}:\n{run.stdout[-4000:]}')
    log=(BUILD/(path.stem+'.log')).read_text(errors='replace')
    if 'Overfull' in log:
        raise RuntimeError(f'Layout warning for {path.name}; inspect {BUILD/(path.stem+".log")}')
    shutil.copy2(BUILD/(path.stem+'.pdf'),path.with_suffix('.pdf'))

def main()->None:
    if not shutil.which('pdflatex'):
        raise RuntimeError('pdflatex is required to rebuild PDFs; the included PDFs can be read without it.')
    BUILD.mkdir(exist_ok=True)
    notes=sorted((ROOT/'proofs').glob('*.tex'))
    with ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(compile_tex,notes))
    compile_tex(ROOT/'Research_manuscript.tex')
    if shutil.which('pandoc'):
        combined=['# Recovered numerical linear algebra proof drafts\n\n'
                  'Seven notes cover eight candidate results. Independent review and source matching are required. '
                  'See [STATUS.md](STATUS.md), [SOURCES.md](SOURCES.md), and '
                  '[the recovery record](research/RECOVERY_AND_CORRECTIONS.md). '
                  'Local IE labels are provisional; six finite-certificate groups pass, while the two '
                  'row-deletion results remain analytic drafts.\n\n']
        for path in notes:
            title=re.search(r'\\title\{([^\n]+)\}',path.read_text()).group(1)
            run=subprocess.run(['pandoc','--from=latex','--to=gfm+tex_math_dollars',
                                '--wrap=none',str(path)],cwd=ROOT,capture_output=True,text=True,timeout=60)
            if run.returncode:
                raise RuntimeError(f'Pandoc failed for {path.name}: {run.stderr}')
            body=re.sub(r'</?div[^>]*>\s*', '', run.stdout)
            body=re.sub(r'^#', '##', body, flags=re.MULTILINE)
            body=re.sub(r'\$\$(.*?)\$\$', lambda m:'\n\n$$\n'+m.group(1).strip()+'\n$$\n\n', body, flags=re.DOTALL)
            text='# '+title+'\n\n'+body
            path.with_suffix('.md').write_text(text,encoding='utf-8')
            # Make footnote identifiers unique before combining standalone notes.
            merged=re.sub(r'\[\^(\w+)\]',lambda m:'[^'+path.stem+'-'+m.group(1)+']',text)
            combined.append('\n\n---\n\n'+merged)
        (ROOT/'Research_manuscript.md').write_text(''.join(combined),encoding='utf-8')
    else:
        print('Pandoc is unavailable; existing Markdown renditions were not changed.')
    print(f'Built {len(notes)} individual PDFs and the combined manuscript.')

if __name__=='__main__': main()
