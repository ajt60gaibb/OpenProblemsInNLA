#!/usr/bin/env python3
"""Bind complete evidence and copy it without changing candidate inputs."""
from pathlib import Path
import hashlib, json, shutil, subprocess

base = Path(__file__).resolve().parent
project = Path('/tmp/nla-lean-mi03-worktree/matrix-inequalities-and-norms/MI-03/lean')
target = project / 'verification/linux-2026-09-12'
manifest_path = base / 'EVIDENCE-MANIFEST.json'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
files = sorted(p for p in base.rglob('*') if p.is_file() and p != manifest_path)
report = base / 'OPERATIONAL-REVIEW.md'
report.write_text(report.read_text().replace('@BOUND_COUNT@', str(len(files))).replace('@TOTAL_COUNT@', str(len(files) + 1)))
manifest_path.write_text(json.dumps({'scope': 'Complete independent MI-03 actual Linux operational evidence. Only this exact outer manifest path is excluded; nested manifests are included.', 'commit': '901ba5ffad3b57557b60c7360df67659d8b8aa21', 'run': 34722618003, 'file_count': len(files), 'files': {str(p.relative_to(base)): {'bytes': p.stat().st_size, 'sha256': sha(p)} for p in files}}, indent=2) + '\n')
subprocess.run(['python3', str(base / 'verify_evidence.py')], check=True)
assert not target.exists(), 'Do not overwrite an existing retained audit'
shutil.copytree(base, target)
subprocess.run(['python3', str(target / 'verify_evidence.py')], check=True)
receipt = json.loads(next((base / 'artifacts/lean-MI-03').glob('verify-*/result.json')).read_text())
for rel, expected in receipt['input_sha256'].items():
    assert sha(project / rel) == expected, rel
print(json.dumps({'report_sha256': sha(report), 'manifest_sha256': sha(manifest_path), 'bound_files': len(files), 'total_files': len(files) + 1, 'all_verified_candidate_inputs_preserved': len(receipt['input_sha256']), 'retained_path': str(target)}, indent=2))
