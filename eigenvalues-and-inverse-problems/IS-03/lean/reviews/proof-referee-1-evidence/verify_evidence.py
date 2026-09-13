"""Offline exact evidence inventory, including its external adjacent report."""
from pathlib import Path
import hashlib
import json

out = Path(__file__).resolve().parent
manifest_path = out / 'EVIDENCE-MANIFEST.json'
manifest = json.loads(manifest_path.read_text())
actual = {str(p.relative_to(out)) for p in out.rglob('*') if p.is_file() and p != manifest_path}
bound = manifest['files']
assert actual == {r for r in bound if not r.startswith('../')}
assert set(bound) - actual == {'../proof-referee-1.md'}
assert len(actual) == manifest['internal_file_count'] and len(bound) == manifest['file_count']
for rel, record in bound.items():
    path = out / rel
    assert path.resolve().is_relative_to(out.parent.resolve()) and not path.is_symlink()
    assert path.stat().st_size == record['bytes'], rel
    assert hashlib.sha256(path.read_bytes()).hexdigest() == record['sha256'], rel
print(json.dumps({'result': 'PASS', 'bound_files': len(bound), 'internal_files': len(actual),
    'outer_manifest_sha256': hashlib.sha256(manifest_path.read_bytes()).hexdigest()}))
