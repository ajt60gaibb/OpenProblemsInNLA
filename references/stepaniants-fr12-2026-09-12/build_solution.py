"""Build the standalone FR-12 proof PDF without leaving TeX auxiliary files."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
PROBLEM = ROOT / 'frames-and-matrix-designs/FR-12'
with tempfile.TemporaryDirectory(prefix='fr12-proof-') as scratch:
    work = Path(scratch)
    shutil.copyfile(PROBLEM / 'solution.tex', work / 'solution.tex')
    command = [os.environ.get('XELATEX', 'xelatex'), '-interaction=nonstopmode',
               '-halt-on-error', 'solution.tex']
    for _ in range(2):
        result = subprocess.run(command, cwd=work, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode:
            raise SystemExit(result.stdout)
    shutil.copyfile(work / 'solution.pdf', PROBLEM / 'solution.pdf')
print('Built frames-and-matrix-designs/FR-12/solution.pdf')
