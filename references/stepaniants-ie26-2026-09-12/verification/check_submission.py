#!/usr/bin/env python3
"""Offline IE-26 source, formula, target, attribution and artifact checks.

This validates conversion and provenance, not the mathematical theorem.
Run from any working directory after final artifacts/checkpoints are frozen.
"""
from pathlib import Path
import hashlib
import io
import json
import re
import tokenize

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RECORD = HERE.parent
DIRECTORY = ROOT / 'linear-systems-and-elimination/IE-26'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def core(text):
    return text[text.index('## 1. Exact target and conclusion'):text.index('## 8.')]


def md_math(text):
    return [re.sub(r'\s+', '', a or b) for a, b in
            re.findall(r'\$\$(.*?)\$\$|\$(.*?)\$', text, re.S)]


def tex_math(text):
    return [re.sub(r'\s+', '', a or b) for a, b in
            re.findall(r'\\\[(.*?)\\\]|\\\((.*?)\\\)', text, re.S)]


frozen = HERE / 'RESULT.md'
assert frozen.stat().st_size == 20755
assert digest(frozen.read_bytes()) == '5ce6d660bb1b22f0c4dec439934e883b3e014708e49a63de2dba2760c939d295'
original_core = core(frozen.read_text())
current_core = core((DIRECTORY / 'solution.md').read_text())
assert original_core == current_core
assert len(original_core.encode()) == 16618
assert digest(original_core.encode()) == '0f9222764933df1602163748f6d8c8755f7e45ab9e25139733d2b92851879f55'

original = (HERE / 'canonical-statement.md').read_text()
current = (DIRECTORY / 'README.md').read_text()
marker = '## Statement\n'
assert original.split(marker, 1)[1] == current.split(marker, 1)[1]
assert '**Status:** Solved' in current

counts = {}
for stem, source_name in [('solution', 'solution.md'), ('problem', 'README.md')]:
    source = (DIRECTORY / source_name).read_text()
    formulas = md_math(source)
    generated = tex_math((DIRECTORY / (stem + '.tex')).read_text())
    assert formulas == generated, (stem, len(formulas), len(generated))
    counts[stem] = len(formulas)

checkpoints = json.loads((HERE / 'source-checkpoints.json').read_text())
for relative, expected in checkpoints['files'].items():
    data = (ROOT / relative).read_bytes()
    assert digest(data) == expected['sha256'] and len(data) == expected['bytes'], relative
registry = (ROOT / 'problem_ids.json').read_bytes()
assert digest(registry) == checkpoints['registry_sha256']
assert len(json.loads(registry)) == 217
assert json.loads(registry)['IE-26'] == 'linear-systems-and-elimination/IE-26/README.md'

# Relative links in the archived canonical snapshot retain their original base.
for source in list(RECORD.rglob('*.md')) + [DIRECTORY/'README.md', DIRECTORY/'solution.md']:
    for link in re.findall(r'\]\(([^)]+)\)', source.read_text()):
        if re.match(r'[a-zA-Z][a-zA-Z0-9+.-]*:', link) or link.startswith('#'):
            continue
        target = link.split('#', 1)[0].strip('<>')
        base = DIRECTORY if source.name in {'canonical-statement.md', 'canonical-target.md'} else source.parent
        assert (base / target).exists(), (str(source.relative_to(ROOT)), link)

for source in list(RECORD.rglob('*')) + [DIRECTORY/name for name in ['README.md','solution.md','solution.tex','problem.tex']]:
    if source.is_file() and source.suffix in ('.md','.txt','.json','.tex','.py'):
        scan_text = source.read_text()
        if source.suffix == '.py':
            # Python matrix-product operators are not contact addresses.
            # Scan all strings/comments for addresses.
            scan_text = '\n'.join(t.string for t in tokenize.generate_tokens(io.StringIO(scan_text).readline)
                                  if t.type in (tokenize.STRING, tokenize.COMMENT))
        assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}', scan_text), str(source)
for name in ['README.md', 'solution.md']:
    text = (DIRECTORY / name).read_text()
    for required in ['George Stepaniants', 'Department of Computing and Mathematical Sciences', 'California Institute of Technology']:
        assert required in text, (name, required)

print(json.dumps({'verdict':'PASS','scope':'provenance and conversion; not a theorem proof',
                  'frozen_proof_sha256':digest(frozen.read_bytes()),
                  'unchanged_core_bytes':len(original_core.encode()),'unchanged_original_target_and_history':True,
                  'ordered_formula_counts':counts,'permanent_ids':217,'frozen_files':len(checkpoints['files']),
                  'local_links':'PASS','author_and_affiliation':'PASS','contact_email_scan':'PASS'},indent=2))
