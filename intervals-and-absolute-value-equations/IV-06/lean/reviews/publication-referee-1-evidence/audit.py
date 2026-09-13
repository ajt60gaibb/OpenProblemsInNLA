"""Independent, read-only IV-06 publication preservation audit.

Author: /root/leancert_examples, an AI agent and IV-06 final math referee 1.
This additional publication role does not add a mathematical referee or rerun Lean.
Only this review's evidence files are written; existing project inputs are read.
"""
from pathlib import Path
from datetime import datetime, timezone
import collections
import hashlib
import json
import re
import subprocess
import yaml
import zipfile

EVIDENCE = Path(__file__).resolve().parent
PROJECT = EVIDENCE.parents[1]
ENTRY = PROJECT.parent
REPO = PROJECT.parents[2]
PUB = PROJECT / 'verification/publication-2026-09-12'
LINUX = PROJECT / 'verification/linux-2026-09-12'
ROOT_OPS = PROJECT / 'verification/root-operational-2026-09-12'
CANDIDATE = '18b5ef3127da0ae4f68e09289f60fd4f6e3d9bcb'
UPSTREAM = '5830ed4fb06da0659414a3deb2a40ad327aca052'
HEAD = '4c075f14209e85ef867eea90eacbea1e05e13a61'
sha = lambda data: hashlib.sha256(data).hexdigest()
digest = lambda path: sha(path.read_bytes())
git = lambda *args: subprocess.check_output(['git', *args], cwd=REPO)
load = lambda path: json.loads(path.read_text())
save = lambda name, data: (EVIDENCE / name).write_text(json.dumps(data, indent=2) + '\n')

assert git('rev-parse', 'HEAD').decode().strip() == HEAD
assert git('merge-base', HEAD, UPSTREAM).decode().strip() == UPSTREAM
before = load(PUB / 'before.json')
assert (before['candidate'], before['upstream'], before['integration']) == (CANDIDATE, UPSTREAM, HEAD)
prefix = PROJECT.relative_to(REPO).as_posix() + '/'
candidate_paths = git('ls-tree', '-r', '--name-only', CANDIDATE, '--', prefix).decode().splitlines()
candidate = {p.removeprefix(prefix): sha(git('show', CANDIDATE + ':' + p)) for p in candidate_paths}
assert len(candidate) == 200 and candidate == before['candidate_inputs']
receipt_path, = (LINUX / 'artifacts/lean-IV-06').rglob('result.json')
receipt = load(receipt_path)
assert receipt['repository_commit'] == CANDIDATE
assert receipt['input_sha256'] == candidate and receipt['result'] == 'comparator-accepted'
changed = {p for p, h in candidate.items() if digest(PROJECT / p) != h}
assert changed == {'README.md', 'formalization.yaml'}, changed
assert digest(PUB / 'archive/README.linux-candidate.md') == candidate['README.md']
assert digest(PUB / 'archive/formalization.linux-candidate.yaml') == candidate['formalization.yaml']

def structural_diff(a, b, path=()):
    if isinstance(a, dict) and isinstance(b, dict):
        assert set(a) == set(b), ('changed metadata keys', path)
        return sum((structural_diff(a[k], b[k], path + (k,)) for k in a), [])
    return [] if a == b else ['.'.join(path)]

previous_manifest = yaml.safe_load((PUB / 'archive/formalization.linux-candidate.yaml').read_text())
manifest = yaml.safe_load((PROJECT / 'formalization.yaml').read_text())
manifest_changes = structural_diff(previous_manifest, manifest)
whitelist = {'status.scope', 'review.status', 'review.notes',
             'review.linux_verification.status', 'review.linux_verification.note'}
assert set(manifest_changes) == whitelist and len(manifest_changes) == 5, manifest_changes
config = load(PROJECT / 'comparator.json')
assert config == receipt['config']
assert config['definition_names'] == []
assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert len(config['theorem_names']) == 8
assert [r['declaration'] for r in manifest['status']['main_results']] == config['theorem_names']
assert [r['declaration'] for r in manifest['alignment']] == config['theorem_names']
for declaration in config['theorem_names']:
    assert ('theorem ' + declaration.removeprefix('NLA.IV06.')) in (PROJECT / 'Solution.lean').read_text()
assert len(load(PROJECT / 'lake-manifest.json')['packages']) == 10

def audit_manifest(root, expected, expected_sha):
    outer = root / 'EVIDENCE-MANIFEST.json'
    assert digest(outer) == expected_sha
    data = load(outer)['files']
    actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p != outer}
    assert actual == set(data) and len(data) == expected
    for rel, record in data.items():
        p = root / rel
        assert not p.is_symlink() and digest(p) == record['sha256'] and p.stat().st_size == record['bytes'], rel
    return {p.relative_to(PROJECT).as_posix(): digest(p) for p in root.rglob('*') if p.is_file()}

ops = audit_manifest(LINUX, 347, 'b4cde7e528bbf53ba50291e73d48ff27d490df228fbc0e9cea0f9d54011bc7d0')
ops.update(audit_manifest(ROOT_OPS, 6, 'f1e635854b86bd567514576fef60eca130be489075f96d56fdd3e3bf45b6f225'))
assert len(ops) == 355 and ops == before['operational_evidence']
assert digest(LINUX / 'OPERATIONAL-REVIEW.md') == '4e212afc2458805a3684748939e46f47dac3e1f6e7576bb5fc8dc591d75ed7c8'
assert digest(ROOT_OPS / 'ROOT-CHECKS.json') == 'bfcea16a79ad3398dc902dbb0ab3ca7014d0f70cf7460db1e7731f1c976a6259'

registry = load(REPO / 'problem_ids.json')
assert len(registry) == 217 and digest(REPO / 'problem_ids.json') == before['problem_ids_sha256']
assert (REPO / 'problem_ids.json').read_bytes() == git('show', UPSTREAM + ':problem_ids.json')
other_pages = {i: digest(REPO / p) for i, p in registry.items() if i != 'IV-06'}
assert other_pages == before['other_canonical'] and len(other_pages) == 216
for i, path in registry.items():
    if i != 'IV-06':
        assert (REPO / path).read_bytes() == git('show', UPSTREAM + ':' + path), i
canonical = (ENTRY / 'README.md').read_text()
target = canonical[canonical.index('## Problem statement'):]
original = git('show', UPSTREAM + ':' + (ENTRY / 'README.md').relative_to(REPO).as_posix()).decode()
assert target == original[original.index('## Problem statement'):]
assert sha(target.encode()) == before['canonical_target_tail_sha256']

def status(text):
    return re.search(r'^\*\*Status:\*\*\s+([^\n]+)', text, re.M).group(1).strip()

counts = collections.Counter(status((REPO / p).read_text()) for p in registry.values())
assert counts == {'Lean verified': 17, 'Solved': 75, 'Open': 53, 'Partially resolved': 72}, counts
old_verified = {i for i, p in registry.items() if status(git('show', UPSTREAM + ':' + p).decode()) == 'Lean verified'}
new_verified = {i for i, p in registry.items() if status((REPO / p).read_text()) == 'Lean verified'}
assert len(old_verified) == 16 and new_verified == old_verified | {'IV-06'}

resolved = (REPO / 'RESOLVED.md').read_text()
old_resolved = git('show', HEAD + ':RESOLVED.md').decode()
assert sha(old_resolved.encode()) == before['resolved_before_sha256']
def split_iv06(text):
    start = text.index('### IV-06 -')
    end = text.index('\n## ', start + 1)
    return text[:start], text[start:end], text[end:]
left, block, right = split_iv06(resolved)
old_left, old_block, old_right = split_iv06(old_resolved)
assert (left, right) == (old_left, old_right)
assert old_block.split('\n\n', 1)[1].rstrip() in block
save('IV-06-RESOLVED-block.json', {'text': block, 'sha256': sha(block.encode())})

for name, text in [('canonical', canonical), ('project README', (PROJECT / 'README.md').read_text()),
                   ('formalization.yaml', (PROJECT / 'formalization.yaml').read_text()), ('RESOLVED block', block)]:
    assert 'George Stepaniants' in text and 'Matthew J. Colbrook' in text
    assert 'Department of Computing and Mathematical Sciences' in text
    assert 'California Institute of Technology' in text and 'Pasadena, California, USA' in text
    assert not re.search(r'[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}', text), name
    assert CANDIDATE in text and '34725713519' in text

run = load(LINUX / 'run-metadata.json')
assert run['id'] == 34725713519 and run['head_sha'] == CANDIDATE
assert run['status'] == 'completed' and run['conclusion'] == 'success'
jobs = load(LINUX / 'jobs.json')['jobs']
assert len(jobs) == 12 and all(j['conclusion'] == 'success' for j in jobs)
assert all(s['conclusion'] == 'success' for j in jobs for s in j['steps'])
axioms = load(LINUX / 'axiom-verification.json')
assert len(axioms['declarations']) == 17
assert all(set(a) == set(config['permitted_axioms']) for a in axioms['declarations'].values())
controls = load(LINUX / 'control-verification.json')
assert controls['theorem_names'] == config['theorem_names']
assert controls['default_kernel_replay'] == controls['statement_comparator'] == 'accepted'
assert controls['fresh_challenge_graph_jobs'] == 1916 and controls['fresh_solution_graph_jobs'] == 2918
assert controls['fresh_dependency_clones'] == 10 and controls['official_mathlib_cache_files'] == 8690
for values in controls['control_runs'].values():
    assert [values[k] for k in ('actual_sandbox_modes', 'sandbox_option_rejections',
                               'actual_raw_kernel_cases', 'actual_comparator_fixtures', 'actual_axiom_rejections')] == [2, 4, 3, 5, 2]

archives = [('lean-IV-06', 10307218980, 'bbe96d9e07020993524329a33ea366ff0ab85707d666b0974bd06c667af0e005', 13),
            ('lean-checker-controls', 10307428276, '3c405009704da285d05939461fec1bb38f8a8fe4f9e7f52339f2da4f689c0529', 10)]
metadata = load(LINUX / 'artifact-metadata.json')['artifacts']
for name, aid, expected, n in archives:
    artifact, = [a for a in metadata if a['id'] == aid]
    assert artifact['digest'] == 'sha256:' + expected and artifact['name'] == name
    archive = LINUX / (name + '.zip')
    assert digest(archive) == expected
    with zipfile.ZipFile(archive) as z:
        assert z.testzip() is None
        members = [f for f in z.infolist() if not f.is_dir()]
        assert len(members) == n
        for f in members:
            assert (LINUX / 'artifacts' / name / f.filename).read_bytes() == z.read(f)
assert digest(LINUX / 'run-logs.zip') == '022aa9a6df6fc50353ba5a9644ef13a5652a21426848c450d7950e5259bd4068'
with zipfile.ZipFile(LINUX / 'run-logs.zip') as z:
    assert z.testzip() is None and len([f for f in z.infolist() if not f.is_dir()]) == 152

checks = load(PUB / 'checks.json')
assert len(checks) == 9 and all(c['exit_code'] == 0 for c in checks)
for record in checks:
    assert digest(PUB / record['log']) == record['log_sha256']
assert 'Ran 17 tests' in (PUB / 'permanent-id-tests.log').read_text()
assert 'PASS (8 declarations)' in (PUB / 'manifest.log').read_text()
assert 'Pages:           3' in (PUB / 'pdfinfo.log').read_text()

save('audit-result.json', {
    'status': 'PASS read-only preservation and publication-claim audit; final publication freeze and PDF visual gate checked separately',
    'utc': datetime.now(timezone.utc).isoformat(), 'candidate': CANDIDATE, 'integration': HEAD,
    'upstream': UPSTREAM, 'candidate_inputs': 200, 'unchanged_nonwrappers': 198,
    'changed_manifest_fields': manifest_changes, 'retained_operational_files': 355,
    'unchanged_other_canonical_pages': 216, 'permanent_registry_entries': 217,
    'counts': dict(counts), 'prior_verified_retained': sorted(old_verified),
    'only_changed_RESOLVED_block': 'IV-06', 'actual_successful_run': run['id'],
    'actual_exports': config['theorem_names'], 'actual_standard_three_reports': 17,
    'existing_validation_checks_reviewed': 9, 'proof_or_dependency_rerun': False,
    'limitations': 'Independent publication review of recorded execution and immutable identity; not a third mathematical review or new Ubuntu run.'})
print('PASS: 200 candidate inputs; 198 nonwrappers; five exact manifest fields; 355 operational files; 217 permanent IDs; only IV-06 promotion.')
