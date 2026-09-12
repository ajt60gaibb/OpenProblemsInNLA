#!/usr/bin/env python3
"""Check frozen artifacts, original targets, formulas and local links; no network."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RECORD = HERE.parent

def digest(data):
    return hashlib.sha256(data).hexdigest()

def md_math(text):
    return [re.sub(r'\s+', '', a or b) for a, b in
            re.findall(r'\$\$(.*?)\$\$|\$(.*?)\$', text, re.S)]

def tex_math(text):
    return [re.sub(r'\s+', '', a or b) for a, b in
            re.findall(r'\\\[(.*?)\\\]|\\\((.*?)\\\)', text, re.S)]

manifest = json.loads((HERE / 'original-package-manifest.json').read_text())
original = RECORD / 'originals/reconstructed-notes'
assert len(manifest) == 6
for relative, expected in manifest.items():
    data = (original / relative).read_bytes()
    assert len(data) == expected['bytes'] and digest(data) == expected['sha256'], relative
for line in (original / 'SHA256SUMS.txt').read_text().splitlines():
    expected, relative = line.split(None, 1)
    relative = relative.strip().lstrip('*')
    assert digest((original / relative).read_bytes()) == expected, relative

counts = {}
for pid in ('SP-11', 'SP-12'):
    directory = ROOT / 'eigenvalues-and-inverse-problems' / pid
    original_target = (HERE / 'original-targets' / (pid + '.md')).read_text()
    current = (directory / 'README.md').read_text()
    marker = '## Problem statement\n'
    assert current.split(marker, 1)[1] == original_target.split(marker, 1)[1], pid
    for stem in ('solution', 'problem'):
        source = directory / ('solution.md' if stem == 'solution' else 'README.md')
        formulas = md_math(source.read_text())
        generated = tex_math((directory / (stem + '.tex')).read_text())
        assert formulas == generated, (pid, stem, len(formulas), len(generated))
        counts[pid + '/' + stem] = len(formulas)

checkpoints = json.loads((HERE / 'source-checkpoints.json').read_text())
for relative, expected in checkpoints['files'].items():
    data = (ROOT / relative).read_bytes()
    assert digest(data) == expected['sha256'] and len(data) == expected['bytes'], relative
assert digest((ROOT / 'problem_ids.json').read_bytes()) == checkpoints['registry_sha256']
assert len(json.loads((ROOT / 'problem_ids.json').read_text())) == 203

# Sources added by this submission and their canonical pages, not unrelated repository content.
sources = list(RECORD.rglob('*.md')) + [ROOT / 'eigenvalues-and-inverse-problems' / p / f
          for p in ('SP-11', 'SP-12') for f in ('README.md', 'solution.md')]
for source in sources:
    for link in re.findall(r'\]\(([^)]+)\)', source.read_text()):
        if re.match(r'[a-zA-Z][a-zA-Z0-9+.-]*:', link) or link.startswith('#'):
            continue
        target = link.split('#', 1)[0].strip('<>')
        link_base = (ROOT / 'eigenvalues-and-inverse-problems' / source.stem
                     if source.parent == HERE / 'original-targets' else source.parent)
        assert (link_base / target).exists(), (source.relative_to(ROOT), link)

# The archived package and published audit contain no personal email addresses.
for source in list(RECORD.rglob('*')) + [ROOT / 'eigenvalues-and-inverse-problems' / p / f
          for p in ('SP-11', 'SP-12') for f in ('README.md', 'solution.md', 'solution.tex', 'problem.tex')]:
    if source.is_file() and source.suffix in ('.md', '.txt', '.json', '.tex', '.py'):
        assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}', source.read_text()), source

print(json.dumps({'verdict': 'PASS', 'preserved_original_files': 6,
                  'supplied_checksums_verified': 5, 'original_targets': 2,
                  'ordered_formula_counts': counts, 'permanent_ids': 203,
                  'frozen_files': len(checkpoints['files']),
                  'local_links': 'PASS', 'personal_email_scan': 'PASS'}, indent=2))
