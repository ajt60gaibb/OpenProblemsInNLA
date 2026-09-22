#!/usr/bin/env python3
"""Read-only bounded integration audit, separate from proof verification."""
from collections import Counter
from pathlib import Path
import hashlib
import json
import re
import subprocess

review = Path(__file__).resolve().parent
repo = review.parents[4]
integration = 'baf14a2dd15b7842f27d57198a483def8347f9b9'
previous = 'c445ad291e9046be5ee43bc5780fceab854c5469'
base = '28efcc2eed621b1b7662f71deac670f96b8ed298'
verified = '1eb284b84ecc0d3c958d022b3e020be7fa111391'
ie21 = 'linear-systems-and-elimination/IE-21'
tr27 = 'tensor-computations/TR-27'
git = lambda *args: subprocess.check_output(['git', *args], cwd=repo)
blob = lambda revision, path: git('show', revision + ':' + path)
sha = lambda data: hashlib.sha256(data).hexdigest()
digest = lambda path: sha(path.read_bytes())
parents = git('show', '-s', '--format=%P', integration).decode().split()
assert parents == [previous, base]
subprocess.run(['git', 'merge-base', '--is-ancestor', verified, integration], cwd=repo, check=True)
for revision, prefix, count in [(previous, ie21, 669), (base, tr27, 320)]:
    paths = git('ls-tree', '-r', '--name-only', revision, '--', prefix).decode().splitlines()
    assert len(paths) == count
    for p in paths:
        expected = blob(revision, p)
        assert blob(integration, p) == expected == (repo / p).read_bytes(), p
    print(f'PASS: all{count} {prefix} files equal reviewed parent Git blobs and current bytes')

registry = 'problem_ids.json'
assert blob(base, registry) == blob(previous, registry) == blob(integration, registry) == (repo / registry).read_bytes()
entries = json.loads((repo / registry).read_text())
assert len(entries) == 217
counts = Counter()
changes = []
for identifier, path in entries.items():
    old, current = blob(base, path), (repo / path).read_bytes()
    assert current == blob(integration, path)
    status = re.search(rb'^\*\*Status:\*\* (.+?)\s*$', current, re.M)[1].decode()
    old_status = re.search(rb'^\*\*Status:\*\* (.+?)\s*$', old, re.M)[1].decode()
    counts[status] += 1
    if old_status != status:
        changes.append((identifier, old_status, status))
    if identifier != 'IE-21':
        assert old == current, identifier
assert changes == [('IE-21', 'Solved', 'Lean verified')]
assert counts == {'Lean verified': 65, 'Solved': 41, 'Partially resolved': 70, 'Open': 41}
for path in ['README.md', 'CATALOG.md']:
    text = (repo / path).read_text()
    assert '**Resolution evidence:** 41 solved (published or independently audited); 65 solved with Lean verification.' in text
    assert '**111 problems with open targets:** 41 open and 70 partially resolved. **106 other retained entries**' in text

renderer = 'tools/render_problems.py'
old = blob(base, renderer).decode()
new = (repo / renderer).read_text()
assert old.replace('{"IE-02", "IE-04", "IE-14", "IV-03"', '{"IE-02", "IE-04", "IE-14", "IE-21", "IV-03"').replace('{"SP-11", "SP-12"}', '{"IE-21", "SP-11", "SP-12"}') == new
outside = {p for p in git('diff', '--name-only', base, integration).decode().splitlines() if not p.startswith(ie21 + '/')}
assert outside == {'README.md', 'CATALOG.md', renderer, 'linear-systems-and-elimination/README.md'}
prior = json.loads((review / 'publication-receipt.json').read_text())
for path, h in prior['publication_files_sha256'].items():
    if path not in {'README.md', 'CATALOG.md', renderer}:
        assert digest(repo / path) == h, path
assert digest(repo / ie21 / 'problem.pdf') == '79bba1583e7cf9ca8282a671defd5d960b910004e24b4959ce6f888458c3ea90'
root_record = json.loads((review.parent / 'publication/root-integration.json').read_text())
assert root_record['PR_base_commit'] == base
assert root_record['previous_IE21_publication_commit'] == previous
assert root_record['cumulative_counts'] == counts
for p, h in root_record['source_file_sha256'].items():
    assert digest(repo / p) == h, p
print('PASS: exact merge parents and verified IE21 source ancestry')
print('PASS: all217 IDs and other canonical pages unchanged from TR27 base; only IE21 newly promoted')
print('PASS: cumulative counts Lean65/Solved41/Partial70/Open41, unchanged111 open targets and106 retained')
print('PASS: shared renderer preserves TR27 exactly plus only the two reviewed IE21 set additions')
print('PASS: PR delta outside IE21 only cumulative root/catalog/category/renderer; previous IE21 artifacts unchanged')
print('SCOPE: integration identity/count review only; no new Lean execution or independent TR27 mathematical re-review')
