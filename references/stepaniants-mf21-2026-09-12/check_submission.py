"""Verify MF-21 reviewed-source binding, target preservation and publication."""
from pathlib import Path
from hashlib import sha256
import json
import os
import re
import subprocess

r = Path(__file__).resolve().parent
w = r.parents[1]
p = w / 'matrix-functions-and-stability/MF-21'
pandoc = os.environ.get('PANDOC', 'pandoc')


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def math_nodes(path, fmt):
    ast = json.loads(subprocess.check_output(
        [pandoc, '-f', fmt, '-t', 'json', str(path)], text=True))
    nodes = []

    def walk(x):
        if isinstance(x, dict):
            if x.get('t') == 'Math':
                nodes.append(re.sub(r'\s+', '', x['c'][1]))
            else:
                for value in x.values():
                    walk(value)
        elif isinstance(x, list):
            for value in x:
                walk(value)
    walk(ast['blocks'])
    return nodes


assert digest(r / 'reviewed-proof.md') == '98eb74a858ad3d2bf5fd0055a92d9c96b9a5e4f4f531972cd429462acb2b44f5'
assert digest(r / 'independent-review.md') == '3c7611724de24ce996ea313041a3d2962134e356ffa776ceef8a3df5560f6c3a'
assert digest(p / 'solution.md') == '6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa'
assert digest(r / 'canonical-statement.md') == '1aac38ed3c7a83dfc3dddb4beeec26fcf117f23f5789b2a374c1332ba4cf359f'
assert (r / 'reviewed-candidate.md').read_bytes() == (r / 'reviewed-proof.md').read_bytes()
assert (r / 'canonical-target.md').read_bytes() == (r / 'canonical-statement.md').read_bytes()
assert (r / 'independent-math-review.md').read_bytes() == (r / 'independent-review.md').read_bytes()

a = (r / 'reviewed-proof.md').read_text()
b = (p / 'solution.md').read_text()
edits = json.loads((r / 'editorial-conversion.json').read_text())
for before, after in edits['explicit_math_delimiter_and_prose_repairs']:
    assert a.count(before) == 1
    a = a.replace(before, after)


def core(text):
    return text[text.index('## 1. Exact conclusion'):text.index('## 6.')]


assert core(a) == core(b)
assert sha256(core(b).encode()).hexdigest() == 'e75264cb480d17a2c32e6876b5949befa70bbf991f6391720cfcb0d65b799012'
base = (r / 'canonical-statement.md').read_text()
canonical = (p / 'README.md').read_text()
original = base[base.index('## Statement'):]
assert canonical.count(original) == 1
assert canonical.splitlines()[0] == base.splitlines()[0]
assert '**Status:** Solved' in canonical
registry = json.loads((w / 'problem_ids.json').read_text())
assert registry['MF-21'] == 'matrix-functions-and-stability/MF-21/README.md'
assert len(registry) == 217

formula_counts = {}
for stem in ['solution', 'problem']:
    md = p / ('solution.md' if stem == 'solution' else 'README.md')
    m = math_nodes(md, 'markdown+tex_math_dollars+raw_tex')
    t = math_nodes(p / (stem + '.tex'), 'latex')
    assert m == t, (stem, len(m), len(t))
    formula_counts[stem] = len(m)

snapshots = {'canonical-statement.md', 'canonical-target.md'}
public_md = [p / 'solution.md', p / 'README.md'] + [
    f for f in r.rglob('*.md') if f.name not in snapshots]
for f in public_md:
    for target in re.findall(r'\]\(([^)]+)\)', f.read_text()):
        if '://' in target or target.startswith('#'):
            continue
        dest = (f.parent / target.split('#', 1)[0]).resolve()
        assert dest.exists(), (str(f), target)

email = re.compile(r'[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}')
texts = []
for f in list(r.rglob('*')) + list(p.iterdir()):
    if not f.is_file() or f.suffix not in ['.md', '.tex', '.json', '.py', '.txt']:
        continue
    assert not email.search(f.read_text()), f
    texts.append(str(f.relative_to(w)))
for stem in ['solution', 'problem']:
    text = subprocess.check_output(['pdftotext', str(p / (stem + '.pdf')), '-'], text=True)
    assert not email.search(text)
    for required in ['George Stepaniants', 'Department of Computing and Mathematical Sciences',
                     'California Institute of Technology']:
        assert required in ' '.join(text.split()), (stem, required)
for required in ['George Stepaniants', 'Department of Computing and Mathematical Sciences',
                 'California Institute of Technology']:
    for text in [b, canonical, (w / 'RESOLVED.md').read_text()]:
        assert required in text

report = {
    'status': 'PASS',
    'reviewed_source_binding': 'PASS',
    'public_source_binding': 'PASS',
    'mathematical_core_identical_after_recorded_editorial_repairs': True,
    'editorial_repair_groups': len(edits['explicit_math_delimiter_and_prose_repairs']),
    'original_target_and_history_retained': True,
    'formulas_identical_in_order': formula_counts,
    'relative_links': 'PASS (historical snapshot navigation explicitly excluded)',
    'author_affiliation': 'PASS',
    'no_contact_email': 'PASS',
    'text_files_checked': len(texts),
    'artifacts': {str(f.relative_to(w)): {'bytes': f.stat().st_size, 'sha256': digest(f)}
                  for f in sorted(p.iterdir()) if f.is_file()}
}
print(json.dumps(report, indent=2))
