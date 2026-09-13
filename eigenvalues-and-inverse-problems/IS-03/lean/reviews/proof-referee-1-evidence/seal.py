"""Seal independent IS-03 final referee evidence; never replace a prior seal."""
from pathlib import Path
import hashlib
import json
import subprocess

out = Path(__file__).resolve().parent
target = out / 'EVIDENCE-MANIFEST.json'
assert not target.exists()
subprocess.run(['python3', str(out / 'final_audit.py')], check=True)
files = sorted(p for p in out.rglob('*') if p.is_file() and p != target)
records = {str(p.relative_to(out)): {'sha256': hashlib.sha256(p.read_bytes()).hexdigest(), 'bytes': p.stat().st_size} for p in files}
report = out.parent / 'proof-referee-1.md'
records['../proof-referee-1.md'] = {'sha256': hashlib.sha256(report.read_bytes()).hexdigest(), 'bytes': report.stat().st_size}
target.write_text(json.dumps({'reviewer': '/root/leancert_examples',
    'verdict': 'APPROVE complete frozen mathematics; actual Linux and publication remain pending',
    'proof_freeze_sha256': '636cdb024f5b73ea61edd518de39ee192a604987aad2b9914c4d7e7eeab672e4',
    'internal_file_count': len(files), 'file_count': len(records),
    'inventory_rule': 'All internal files except only this exact outer manifest, plus the adjacent report. Nested manifests are not filtered by basename.',
    'files': records}, indent=2) + '\n')
subprocess.run(['python3', str(out / 'verify_evidence.py')], check=True)
print(json.dumps({'report_sha256': hashlib.sha256(report.read_bytes()).hexdigest(),
    'evidence_manifest_sha256': hashlib.sha256(target.read_bytes()).hexdigest()}, indent=2))
