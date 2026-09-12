"""Check the MI-21 publication without rewriting frozen proof/evidence files."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

W = Path('/tmp/nla-lean-mi21-worktree')
P = W / 'matrix-inequalities-and-norms/MI-21'
L = P / 'lean'
OUT = L / 'verification/publication-2026-09-12'
before = json.loads((OUT / 'before.json').read_text())
BASE = before['merge_head']


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(*args):
    return subprocess.check_output(['git', *args], cwd=W)


def blob(rel):
    return git('show', BASE + ':' + rel)


protected = {}
for rel, entry in before['original_project'].items():
    if entry['publication_edit_permitted']:
        continue
    assert sha((W / rel).read_bytes()) == entry['sha256'], rel
    protected[rel] = entry['sha256']
assert len(protected) == 79
for name in ['solution.tex', 'solution.md', 'solution.pdf']:
    assert sha((P / name).read_bytes()) == before['canonical_sources'][name]['sha256'], name
original = (OUT / 'original-target.md').read_text()
assert (P / 'README.md').read_text().split('## Problem statement', 1)[1] == original
assert blob('matrix-inequalities-and-norms/MI-21/README.md').decode().split(
    '## Problem statement', 1)[1] == original
assert (W / 'problem_ids.json').read_bytes() == blob('problem_ids.json')
registry = json.loads((W / 'problem_ids.json').read_text())
other = []
counts = {}
verified = []
for ident, rel in registry.items():
    text = (W / rel).read_text()
    status = re.search(r'^\*\*Status:\*\* (.+?)\s*$', text, re.M).group(1)
    counts[status] = counts.get(status, 0) + 1
    if status == 'Lean verified':
        verified.append(ident)
    if ident != 'MI-21':
        assert (W / rel).read_bytes() == blob(rel), ident
        other.append(ident)
assert len(other) == 216
assert counts == {'Solved': 82, 'Open': 57, 'Partially resolved': 71, 'Lean verified': 7}
assert sorted(verified) == ['IE-01', 'IE-18', 'IE-19', 'MI-19', 'MI-21', 'RA-03', 'TR-01']

linux = L / 'verification/linux-2026-09-12'
evidence = json.loads((linux / 'EVIDENCE-MANIFEST.json').read_text())
for rel, entry in evidence['files'].items():
    data = (linux / rel).read_bytes()
    assert sha(data) == entry['sha256'] and len(data) == entry['bytes'], rel
assert sha((linux / 'EVIDENCE-MANIFEST.json').read_bytes()) == (
    '23e54ef671b364d1c04c0b232427458b0c77159b353c1bbf13663156058f81c4')
assert len(evidence['files']) == 58
unchanged_harness = {}
for rel in git('ls-tree', '-r', '--name-only', BASE, '--', 'tools/lean', 'docs/lean',
               '.github/workflows/lean-verification.yml').decode().splitlines():
    assert (W / rel).read_bytes() == blob(rel), rel
    unchanged_harness[rel] = sha(blob(rel))

# Check only publishable files. Ignored fresh local reviewer artifacts and the
# private cloned .lake cache are deliberately retained locally, never staged.
eligible = set(git('ls-files', '--cached', '--others', '--exclude-standard', '--',
                  'matrix-inequalities-and-norms/MI-21/lean').decode().splitlines())
for rel in eligible:
    q = Path(rel)
    assert '.lake' not in q.parts and q.suffix not in {'.olean', '.ilean', '.o', '.so', '.a'}, rel

for q in [P / 'README.md', L / 'README.md']:
    for target in re.findall(r'\]\(([^)]+)\)', q.read_text()):
        if re.match(r'^[A-Za-z][A-Za-z0-9+.-]*:', target) or target.startswith('#'):
            continue
        path = target.split('#', 1)[0]
        assert not path or (q.parent / path).resolve().exists(), (q, target)

files = ['CATALOG.md', 'README.md', 'RESOLVED.md',
         'matrix-inequalities-and-norms/README.md',
         'matrix-inequalities-and-norms/MI-21/README.md',
         'matrix-inequalities-and-norms/MI-21/problem.tex',
         'matrix-inequalities-and-norms/MI-21/problem.pdf',
         'matrix-inequalities-and-norms/MI-21/lean/README.md',
         'matrix-inequalities-and-norms/MI-21/lean/formalization.yaml']
identities = {f: {'sha256': sha((W / f).read_bytes()), 'bytes': (W / f).stat().st_size}
              for f in files}
record = {
    'verdict': 'PASS', 'verified_commit': before['verified_commit'],
    'integrated_upstream': BASE, 'head_remains': git('rev-parse', 'HEAD').decode().strip(),
    'merge_pending_no_commit': True, 'original_inputs_preserved': protected,
    'original_target_and_informal_proof_unchanged': True,
    'other_canonical_pages_identical_to_upstream': len(other),
    'counts': counts, 'lean_verified_ids': sorted(verified),
    'harness_and_document_files_unchanged': unchanged_harness,
    'original_linux_manifest_unchanged': True,
    'original_linux_evidence_files_verified': len(evidence['files']),
    'local_publication_links_exist': True,
    'publishable_project_has_no_build_artifacts': True,
    'publication_files': identities,
}
(OUT / 'integrity.json').write_text(json.dumps(record, indent=2) + '\n')
print('PASS: 79 original proof/config/review inputs preserved; 216 other canonical pages unchanged.')
print('PASS: original target and informal proof unchanged; all 58 original Linux evidence members intact.')
print('Counts:', counts, '; verified IDs:', ', '.join(sorted(verified)))
for name in ['problem.pdf', 'problem.tex']:
    print(name, sha((P / name).read_bytes()), (P / name).stat().st_size)
