#!/usr/bin/env python3
"""Recheck the seven supplied certificate programs using only Python 3's standard library."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
JOBS = [
    ('wave_kernel_certificate.py', ['results/wave_kernel_finite_certificate.json', '--verify']),
    ('gdn_certificate.py', ['results/gdn_certificate.json', '--verify']),
    ('nano_rank_certificate.py', ['--output', 'results/nano_rank_certificate.json', '--verify']),
    ('word_equation_certificate.py', ['results/word_equation_certificate.json', '--verify']),
    ('word_equation_interval_certificate.py', ['results/word_equation_interval_certificate.json', '--verify']),
    ('polynomial_coverage_independent.py', ['results/degree42_certificate.json', '--output', 'results/degree42_independent_certificate.json', '--verify']),
    ('word_equation_interval_independent.py', ['results/word_equation_interval_certificate.json', '--output', 'results/word_equation_interval_independent_certificate.json', '--verify']),
]


def check(job):
    script, args = job
    result = subprocess.run([sys.executable, '-X', 'utf8', '-B', str(ROOT / 'code' / script), *args],
                            cwd=ROOT, capture_output=True, text=True, encoding='utf-8')
    if result.returncode:
        raise RuntimeError(script + '\n' + result.stdout + result.stderr)
    return script + ': PASS'


if __name__ == '__main__':
    with ThreadPoolExecutor(max_workers=4) as pool:
        for result in pool.map(check, JOBS):
            print(result, flush=True)
