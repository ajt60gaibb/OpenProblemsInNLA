"""Seal only this independent referee's final report and evidence.

No mathematical, historical, other-referee or publication file is written.
The exact outer manifest, not every file with its basename, is excluded.
"""
from pathlib import Path
import datetime, hashlib, json, subprocess

E = Path(__file__).resolve().parent
P = E.parents[1]
W = P.parents[2]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
report = P / 'reviews/final-referee-1.md'
outer = E / 'EVIDENCE-MANIFEST.json'
assert not outer.exists(), 'The sealed evidence is immutable; do not replace it.'
proof = json.loads((P / 'verification/proof-freeze.json').read_text())
statement = json.loads((P / 'reviews/statement-freeze.json').read_text())
for record in (proof, statement):
    for rel, digest in record['files'].items():
        assert sha(P / rel) == digest, rel
    for rel, digest in record['source_files'].items():
        raw = subprocess.check_output(['git', '-C', str(W), 'show', record['base'] + ':' + rel])
        assert hashlib.sha256(raw).hexdigest() == digest
        assert (W / rel).read_bytes() == raw
        assert subprocess.check_output(['git', '-C', str(W), 'rev-parse', record['base'] + ':' + rel]).decode().strip() == record['source_git_blobs'][rel]
assert not subprocess.check_output(['git', '-C', str(W), 'diff', '--name-only'])
assert not subprocess.check_output(['git', '-C', str(W), 'diff', '--cached', '--name-only'])
audit = json.loads((E / 'audit-result.json').read_text())
assert audit['verdict'].startswith('PASS independent final mathematical')
assert 'APPROVE the complete frozen mathematical implementation' in report.read_text()
receipt = {
    'verdict': 'PASS: all frozen input identities preserved at independent review seal',
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'project_inputs': len(proof['files']),
    'statement_inputs': len(statement['files']),
    'original_Git_sources': len(proof['source_files']),
    'proof_freeze_sha256': sha(P / 'verification/proof-freeze.json'),
    'statement_freeze_sha256': sha(P / 'reviews/statement-freeze.json'),
    'report_sha256': sha(report),
    'audit_sha256': sha(E / 'audit-result.json'),
    'tracked_changes': False,
    'publication_or_Linux_approval': False,
}
(E / 'final-preservation.json').write_text(json.dumps(receipt, indent=2) + '\n')
inputs = sorted(p for p in E.rglob('*') if p.is_file() and p.resolve() != outer.resolve())
assert all(not p.is_symlink() for p in inputs)
files = {str(p.relative_to(E)): {'sha256': sha(p), 'bytes': p.stat().st_size} for p in inputs}
files['../final-referee-1.md'] = {'sha256': sha(report), 'bytes': report.stat().st_size}
manifest = {
    'kind': 'RA-08 independent final mathematical referee 1 evidence',
    'verdict': 'APPROVE mathematical implementation; later Linux and publication gates pending',
    'reviewer': '/root/leancert_examples; no RA08 statement or proof authorship',
    'self_exclusion': 'Only this exact EVIDENCE-MANIFEST.json; nested manifests, if any, are included.',
    'report': '../final-referee-1.md',
    'files': files,
    'file_count': len(files),
}
outer.write_text(json.dumps(manifest, indent=2) + '\n')
for rel, row in files.items():
    assert sha(E / rel) == row['sha256'] and (E / rel).stat().st_size == row['bytes']
print(json.dumps({'report_sha256': sha(report), 'evidence_manifest_sha256': sha(outer),
                  'bound_files': len(files), 'with_outer': len(files) + 1,
                  'preservation_sha256': sha(E / 'final-preservation.json')}, indent=2))
