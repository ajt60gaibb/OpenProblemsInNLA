"""IE-23 exact expected input check; no Linux verdict follows from this script.

Adapted from the MI-03 operational preflight by /root/formal_review_standards.
This reviewer authored IE-23's proof; independent operational acceptance and
the two already completed independent mathematical reviews remain distinct.
"""
from pathlib import Path
import hashlib
import json
import subprocess

OUT = Path(__file__).resolve().parent
CTX = json.loads((OUT / 'context.json').read_text())
WT = Path(CTX['worktree'])
PROJECT = CTX['project']
P = WT / PROJECT
COMMIT = CTX['commit']
BASE = CTX['source_base']
sha = lambda b: hashlib.sha256(b).hexdigest()
git = lambda *a: subprocess.check_output(['git', '-C', str(WT), *a])
load = lambda r: json.loads((P / r).read_text())
assert git('rev-parse', 'HEAD').decode().strip() == COMMIT
assert not git('status', '--short'), 'Preflight requires the original clean candidate'
raw_commit = git('cat-file', 'commit', COMMIT)
for line in raw_commit.splitlines():
    if line.startswith((b'author ', b'committer ')):
        assert b'George Stepaniants <>' in line
paths = git('ls-tree', '-r', '--name-only', COMMIT, '--', PROJECT).decode().splitlines()
assert len(paths) == CTX['expected_input_count'] == 190
files = {}
for name in paths:
    data = git('show', COMMIT + ':' + name)
    assert (WT / name).read_bytes() == data, name
    files[name[len(PROJECT) + 1:]] = {'sha256': sha(data), 'bytes': len(data)}
freeze_bytes = (P / 'reviews/proof-freeze.json').read_bytes()
assert sha(freeze_bytes) == CTX['proof_freeze_sha256']
freeze = json.loads(freeze_bytes)
pack = load('verification/linux-candidate-2026-09-12/packaging-record.json')
archive = 'verification/linux-candidate-2026-09-12/README.statement.md'
for name, r in freeze['files'].items():
    assert files[archive if name == 'README.md' else name] == r, name
assert len(freeze['files']) == 104
for name, h in freeze['source_files'].items():
    data = git('show', COMMIT + ':' + name)
    assert data == git('show', BASE + ':' + name) == (WT / name).read_bytes()
    assert sha(data) == h, name
for name, h in pack['review_reports_preserved'].items():
    assert files[name]['sha256'] == h
for name, h in pack['metadata_sha256'].items():
    assert files[name]['sha256'] == h
assert files['comparator.json']['sha256'] == pack['comparator_sha256']
assert files['reviews/statement-config-supplement.json']['sha256'] == pack['configuration_supplement_sha256']
config = load('comparator.json')
assert config['theorem_names'] == freeze['completed_exports'] == pack['exports']
assert len(config['theorem_names']) == 8
assert config['definition_names'] == []
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']

def check_manifest(path, expected_hash, complete=True):
    raw = path.read_bytes()
    assert sha(raw) == expected_hash
    records = json.loads(raw)['files']
    actual = {str(f.relative_to(path.parent)) for f in path.parent.rglob('*')
              if f.is_file() and f != path}
    # Parent report paths in reviewer manifests are deliberate; keep them bound
    # while requiring the exact complete set of internal evidence files.
    internal = {r for r in records if not r.startswith('../')}
    if complete:
        assert actual == internal, str(path)
    for r, record in records.items():
        f = path.parent / r
        assert f.resolve().is_relative_to(P.resolve()), r
        assert f.stat().st_size == record['bytes']
        assert sha(f.read_bytes()) == record['sha256']
    return {'bound_files': len(records), 'internal_files': len(internal)}

review_inventories = {}
for name, r in pack['review_evidence_preserved'].items():
    review_inventories[name] = check_manifest(P / name, r['sha256'])
root_manifest = P / 'verification/linux-candidate-2026-09-12/ROOT-EVIDENCE-MANIFEST.json'
root_inventory = check_manifest(root_manifest, CTX['root_packaging_manifest_sha256'])
assert root_inventory['bound_files'] == 22
historical = P / 'verification/linux-candidate-2026-09-12/EVIDENCE-MANIFEST.json'
historical_inventory = check_manifest(historical, 'e4ea6506d3458e620fb6d3dc27587411c0ee3983b133d78b454fd51495a3deaa', complete=False)
assert historical_inventory['bound_files'] == 18
record = {
    'status': 'Expected committed input identities PASS; actual Linux result and operational verdict pending',
    'commit': COMMIT, 'run': CTX['run'], 'project': PROJECT,
    'tracked_input_count': len(files), 'all_worktree_inputs_match_commit': True,
    'blank_author_and_committer_emails': True,
    'preserved_nonREADME_proof_freeze_files': 103,
    'original_source_count': len(freeze['source_files']),
    'unchanged_report_hashes': pack['review_reports_preserved'],
    'review_evidence_complete_inventories': review_inventories,
    'root_candidate_complete_inventory': root_inventory,
    'historical_preparer_subinventory': historical_inventory,
    'role': CTX['role'], 'config': config, 'input_files': files}
(OUT / 'preflight.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({k: record[k] for k in ['status', 'tracked_input_count', 'preserved_nonREADME_proof_freeze_files', 'original_source_count']}))
