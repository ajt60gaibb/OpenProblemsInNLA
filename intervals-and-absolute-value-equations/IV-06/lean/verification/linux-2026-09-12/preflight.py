"""Read-only IV-06 expected-input preparation. No Linux outcome is inferred."""
from pathlib import Path
import datetime, hashlib, json, subprocess

out = Path(__file__).resolve().parent
repo = Path('/tmp/nla-lean-iv06-worktree')
project_rel = 'intervals-and-absolute-value-equations/IV-06/lean'
project = repo/project_rel
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
git = lambda *args: subprocess.check_output(['git', '-C', str(repo), *args])
freeze_path = project/'verification/proof-freeze.json'
assert sha(freeze_path) == '5bc8cfd590e82a27807ad5f6832c0cc5d634832979241f80eb30d8d76eaaa673'
freeze = json.loads(freeze_path.read_text())
pack_path = project/'verification/linux-candidate-2026-09-12/integrity.json'
pack = json.loads(pack_path.read_text())
archive = 'verification/linux-candidate-2026-09-12/README.statement.md'
for rel, record in freeze['files'].items():
    target = project/(archive if rel == 'README.md' else rel)
    assert sha(target) == record['sha256'] and target.stat().st_size == record['bytes'], rel
sources = {}
for rel, expected in freeze['source_files'].items():
    data = (repo/rel).read_bytes()
    assert hashlib.sha256(data).hexdigest() == expected
    assert data == git('show', freeze['source_commit']+':'+rel)
    sources[rel] = {'sha256': expected,
                   'git_blob': git('rev-parse', freeze['source_commit']+':'+rel).decode().strip()}
reports = pack['review_reports_and_manifests']
for rel, expected in reports.items():
    assert sha(project/rel) == expected, rel
for manifest_rel in pack['verified_review_evidence_counts']:
    manifest_path = project/manifest_rel
    manifest = json.loads(manifest_path.read_text())
    files = manifest['files']
    actual = {p.relative_to(manifest_path.parent).as_posix()
              for p in manifest_path.parent.rglob('*') if p.is_file() and p != manifest_path}
    if manifest_rel == 'reviews/proof-referee-2-root-evidence/EVIDENCE-MANIFEST.json':
        actual.add('../proof-referee-2.md')
    assert actual == set(files)
    assert len(files) == pack['verified_review_evidence_counts'][manifest_rel]
    for rel, record in files.items():
        path = manifest_path.parent/rel
        assert sha(path) == record['sha256'] and path.stat().st_size == record['bytes'], rel
config = json.loads((project/'comparator.json').read_text())
assert config['theorem_names'] == freeze['completed_exports'] == pack['exact_export_names']
assert config['definition_names'] == []
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
assert len(config['theorem_names']) == 8
assert sha(project/'README.md') == pack['current_README_sha256']
assert sha(project/'formalization.yaml') == pack['formalization_yaml_sha256']
record = {
    'phase': 'expected inputs only; immutable candidate and actual run details awaited',
    'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'project': project_rel, 'base': freeze['source_commit'],
    'reviewer': '/root/formal_review_standards',
    'reviewer_role': 'Independent operational reviewer and prior statement referee 2; neither proof author nor final proof referee.',
    'proof_freeze_sha256': sha(freeze_path), 'proof_freeze_file_count': len(freeze['files']),
    'historical_README_archive': archive,
    'preserved_nonREADME_proof_freeze_files': len(freeze['files'])-1,
    'original_sources': sources, 'reports_and_manifests': reports,
    'config': config, 'package_manifest_sha256': sha(project/'lake-manifest.json'),
    'packaging_integrity_sha256': sha(pack_path),
    'candidate_manifest_sha256': sha(project/'verification/linux-candidate-2026-09-12/EVIDENCE-MANIFEST.json'),
    'expected_kernel_assertions': freeze['kernel_and_standard_three_checks'],
    'local_dependency_build_copy_or_download': False, 'Linux_success_claim': False}
(out/'preflight.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps({k: record[k] for k in ['phase', 'proof_freeze_file_count',
                                       'preserved_nonREADME_proof_freeze_files',
                                       'expected_kernel_assertions']}))
