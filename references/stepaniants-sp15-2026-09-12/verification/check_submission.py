#!/usr/bin/env python3
"""Offline SP-15 provenance, source, formula, target, artifact and link checks."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RECORD = HERE.parent
DIRECTORY = ROOT / 'eigenvalues-and-inverse-problems/SP-15'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def core(text):
    return text[text.index('## Exact target and conclusion'):text.index('## 5. Scope, attribution, and primary sources')]


def md_math(text):
    return [re.sub(r'\s+', '', a or b) for a, b in
            re.findall(r'\$\$(.*?)\$\$|\$(.*?)\$', text, re.S)]


def tex_math(text):
    return [re.sub(r'\s+', '', a or b) for a, b in
            re.findall(r'\\\[(.*?)\\\]|\\\((.*?)\\\)', text, re.S)]


frozen = HERE / 'RESULT.md'
assert frozen.stat().st_size == 9440
assert digest(frozen.read_bytes()) == 'd992da0546924d7fbc9f1bb0e89e00b1442ec3c3045c739722c9767078ce40c1'
original_core = core(frozen.read_text())
current_core = core((DIRECTORY / 'solution.md').read_text())
assert original_core == current_core
assert len(original_core.encode()) == 7308
assert digest(original_core.encode()) == 'b93675c67c4756099e5d0c169a02a789da304380e99fb0976a5b042b94a20722'

original = (HERE / 'canonical-statement.md').read_text()
current = (DIRECTORY / 'README.md').read_text()
marker = '## Context and notation\n'
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
assert json.loads(registry)['SP-15'] == 'eigenvalues-and-inverse-problems/SP-15/README.md'

# Every submission Markdown link must exist locally, excluding external URLs/anchors.
for source in list(RECORD.rglob('*.md')) + [DIRECTORY/'README.md', DIRECTORY/'solution.md']:
    for link in re.findall(r'\]\(([^)]+)\)', source.read_text()):
        if re.match(r'[a-zA-Z][a-zA-Z0-9+.-]*:', link) or link.startswith('#'):
            continue
        target = link.split('#', 1)[0].strip('<>')
        base = DIRECTORY if source == HERE/'canonical-statement.md' else source.parent
        assert (base / target).exists(), (str(source.relative_to(ROOT)), link)

# Published user attribution contains the allowed name and affiliation, no contact email.
for source in list(RECORD.rglob('*')) + [DIRECTORY/name for name in ['README.md','solution.md','solution.tex','problem.tex']]:
    if source.is_file() and source.suffix in ('.md','.txt','.json','.tex','.py'):
        assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',source.read_text()), str(source)
for name in ['README.md', 'solution.md']:
    text = (DIRECTORY / name).read_text()
    for required in ['George Stepaniants', 'Department of Computing and Mathematical Sciences', 'California Institute of Technology']:
        assert required in text, (name, required)

print(json.dumps({'verdict':'PASS','frozen_proof_sha256':digest(frozen.read_bytes()),
                  'unchanged_core_bytes':len(original_core.encode()),'unchanged_original_target':True,
                  'ordered_formula_counts':counts,'permanent_ids':217,'frozen_files':len(checkpoints['files']),
                  'local_links':'PASS','author_and_affiliation':'PASS','contact_email_scan':'PASS'},indent=2))
