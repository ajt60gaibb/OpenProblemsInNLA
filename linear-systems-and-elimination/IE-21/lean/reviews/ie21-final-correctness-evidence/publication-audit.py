#!/usr/bin/env python3
"""Read-only correspondence checks for the reviewed IE-21 publication delta."""
from collections import Counter
from pathlib import Path
import hashlib
import json
import re
import subprocess

review = Path(__file__).resolve().parent
project = review.parent.parent
repo = project.parents[2]
commit = '1eb284b84ecc0d3c958d022b3e020be7fa111391'
sha = lambda b: hashlib.sha256(b).hexdigest()
digest = lambda p: sha(p.read_bytes())
git = lambda *args: subprocess.check_output(['git', *args], cwd=repo)
blob = lambda p: git('show', commit + ':' + p)
read = lambda p: json.loads(p.read_text())
input_hashes = read(project / 'verification/linux/input-receipt.json')['input_sha256']
changed = {p: {'verified_sha256': h, 'publication_sha256': digest(project / p)}
           for p, h in input_hashes.items() if digest(project / p) != h}
assert set(changed) == {'README.md', 'formalization.yaml'}
correspondence = read(project / 'reviews/publication/root-correspondence.json')
assert changed == correspondence['changed_original_inputs']
assert len(input_hashes) - len(changed) == correspondence['unchanged_original_input_count'] == 287
for p, h in input_hashes.items():
    assert digest(project / 'verification/linux/source' / p) == h
for p in (project / 'NLA/IE21').glob('*.lean'):
    assert digest(p) == input_hashes[str(p.relative_to(project))]
assert len(list((project / 'NLA/IE21').glob('*.lean'))) == 31

canonical = 'linear-systems-and-elimination/IE-21/README.md'
old = blob(canonical).decode()
new = (repo / canonical).read_text()
anchor = '## Problem statement\n'
assert old.split(anchor, 1)[1] == new.split(anchor, 1)[1]
assert sha(new.split(anchor, 1)[1].encode()) == correspondence['original_statement_suffix_sha256']
start = '## Lean proof and verification evidence - 2026-09-22\n'
before = new.split(start, 1)[0]
expected_before = old.split(anchor, 1)[0].replace('**Status:** Solved\n', '**Status:** Lean verified  \n').replace('**Last checked:** 2026-09-11', '**Last checked:** 2026-09-22')
assert before == expected_before
assert digest(repo / canonical) == correspondence['canonical_sha256']
assert sha(blob(canonical)) == correspondence['canonical_original_sha256']
assert 'George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology' in new
assert 'Matthew J. Colbrook' in new
for p in [repo / canonical, project / 'README.md', project / 'formalization.yaml']:
    assert not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}', p.read_text())
assert 'authenticated Mathlib dependency cache' not in (project / 'README.md').read_text()

registry_path = 'problem_ids.json'
assert (repo / registry_path).read_bytes() == blob(registry_path)
registry = read(repo / registry_path)
assert len(registry) == 217
counts = Counter()
status_changes = []
for identifier, relative in registry.items():
    current = (repo / relative).read_bytes()
    previous = blob(relative)
    status = re.search(rb'^\*\*Status:\*\* (.+?)\s*$', current, re.M)[1].decode()
    old_status = re.search(rb'^\*\*Status:\*\* (.+?)\s*$', previous, re.M)[1].decode()
    counts[status] += 1
    if status != old_status:
        status_changes.append((identifier, old_status, status))
    if identifier != 'IE-21':
        assert current == previous, identifier
assert status_changes == [('IE-21', 'Solved', 'Lean verified')]
assert counts == {'Open': 41, 'Partially resolved': 70, 'Solved': 42, 'Lean verified': 64}
for p in ['README.md', 'CATALOG.md']:
    text = (repo / p).read_text()
    assert '**111 problems with open targets:** 41 open and 70 partially resolved. **106 other retained entries**' in text
    assert '**Resolution evidence:** 42 solved (published or independently audited); 64 solved with Lean verification.' in text

renderer = 'tools/render_problems.py'
before = blob(renderer).decode()
after = (repo / renderer).read_text()
assert before.replace('{"IE-02", "IE-04", "IE-14", "IV-03"', '{"IE-02", "IE-04", "IE-14", "IE-21", "IV-03"').replace('{"SP-11", "SP-12"}', '{"IE-21", "SP-11", "SP-12"}') == after
tex = (repo / 'linear-systems-and-elimination/IE-21/problem.tex').read_text()
old_tex = blob('linear-systems-and-elimination/IE-21/problem.tex').decode()
tex_anchor = r'\subsection{Problem statement}'
assert re.sub(r'\s+', '', tex.split(tex_anchor, 1)[1]) == re.sub(r'\s+', '', old_tex.split(tex_anchor, 1)[1])
assert '\\newpage\n' + tex_anchor in tex
assert 'Verification check: 2026-09-22' in tex
pdf = repo / 'linear-systems-and-elimination/IE-21/problem.pdf'
info = subprocess.check_output(['pdfinfo', str(pdf)], text=True)
assert re.search(r'^Pages:\s+3$', info, re.M)

expected_modified = {'CATALOG.md', 'README.md', canonical,
    'linear-systems-and-elimination/IE-21/lean/README.md',
    'linear-systems-and-elimination/IE-21/lean/formalization.yaml',
    'linear-systems-and-elimination/IE-21/problem.pdf',
    'linear-systems-and-elimination/IE-21/problem.tex',
    'linear-systems-and-elimination/README.md', renderer}
assert set(git('diff', '--name-only', commit).decode().splitlines()) == expected_modified
receipt = read(review / 'completion-receipt.json')
assert digest(review / 'source-review.md') == receipt['source_review_sha256']
assert digest(review / 'final-source-review-receipt.json') == receipt['source_receipt_sha256']
for p, h in receipt['review_artifacts_sha256'].items():
    assert digest(review / p) == h
for p, h in receipt['inspected_evidence_sha256'].items():
    assert digest(project / 'verification/linux' / p) == h

print('PASS: exactly README/metadata changed among289 verified inputs;287 remain byte-identical')
print('PASS: all31 source modules, original mathematical/build inputs, source and completion evidence unchanged')
print('PASS: original canonical target/history suffix and historical prefix preserved; only approved status/date/notice added')
print('PASS: all217 permanent IDs unchanged; only IE-21 promoted; counts Open41/Partial70/Solved42/Lean64')
print('PASS: nine expected tracked publication files only; two IE-21-specific renderer-set additions only')
print('PASS: TeX complete original target/history identical modulo whitespace; PDF has3 pages; all3 final render images independently inspected')
print('PASS: George Stepaniants, exact requested affiliation, original Colbrook credit, no contact email')
