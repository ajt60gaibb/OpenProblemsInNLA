"""Seal/copy the IE-23 operational evidence, preserving every candidate byte.

Adapted from the MI-03 sealing driver by /root/formal_review_standards.
Only the exact outer manifest path excludes itself; nested manifests remain.
This implementing agent's operational verdict awaits independent acceptance.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess

base = Path(__file__).resolve().parent
ctx = json.loads((base / 'context.json').read_text())
project = Path(ctx['worktree']) / ctx['project']
target = project / 'verification/linux-2026-09-12'
assert not target.exists(), 'Never overwrite a sealed audit'
manifest_path = base / 'EVIDENCE-MANIFEST.json'
assert not manifest_path.exists(), 'Never overwrite a sealed manifest'
receipt = json.loads(next((base / 'artifacts/lean-IE-23').glob('verify-*/result.json')).read_text())
assert len(receipt['input_sha256']) == ctx['expected_input_count'] == 190
run = json.loads((base / 'run-metadata.json').read_text())
assert run['status'] == 'completed' and run['conclusion'] == 'success'
assert run['head_sha'] == ctx['commit']
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for rel, h in receipt['input_sha256'].items():
    assert sha(project / rel) == h, rel
files = sorted(p for p in base.rglob('*') if p.is_file() and p != manifest_path)
report = base / 'OPERATIONAL-REVIEW.md'
report.write_text(report.read_text().replace('@BOUND_COUNT@', str(len(files))).replace('@TOTAL_COUNT@', str(len(files) + 1)))
manifest_path.write_text(json.dumps({
    'scope': 'Complete actual IE-23 Ubuntu operational evidence; the proof-author inspector does not count as another independent mathematical referee. Coordinator independent acceptance is separate.',
    'reviewer_role': ctx['role'], 'commit': ctx['commit'], 'run': ctx['run'],
    'file_count': len(files),
    'inventory_rule': 'Only this exact outer manifest path excludes itself. All nested manifests, original archives and source snapshots are included.',
    'files': {str(p.relative_to(base)): {'bytes': p.stat().st_size, 'sha256': sha(p)} for p in files}}, indent=2) + '\n')
subprocess.run(['python3', str(base / 'verify_evidence.py')], check=True)
shutil.copytree(base, target)
subprocess.run(['python3', str(target / 'verify_evidence.py')], check=True)
for rel, h in receipt['input_sha256'].items():
    assert sha(project / rel) == h, rel
print(json.dumps({'report_sha256': sha(report), 'manifest_sha256': sha(manifest_path),
    'bound_files': len(files), 'total_files': len(files) + 1,
    'verified_candidate_inputs_preserved': len(receipt['input_sha256']),
    'retained_path': str(target)}, indent=2))
