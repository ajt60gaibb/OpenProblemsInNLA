"""Verify the complete retained evidence, including every nested manifest."""
from pathlib import Path
import hashlib
import json

base = Path(__file__).resolve().parent
manifest_path = base / 'EVIDENCE-MANIFEST.json'
manifest = json.loads(manifest_path.read_text())
actual = {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file() and p != manifest_path}
assert actual == set(manifest['files'])
assert len(actual) == manifest['file_count']
for rel, record in manifest['files'].items():
    path = base / rel
    assert not path.is_symlink() and path.resolve().is_relative_to(base.resolve()), rel
    assert path.stat().st_size == record['bytes'], rel
    assert hashlib.sha256(path.read_bytes()).hexdigest() == record['sha256'], rel
print(json.dumps({'result': 'PASS', 'bound_files': len(actual),
    'total_files_including_outer_manifest': len(actual) + 1,
    'outer_manifest_sha256': hashlib.sha256(manifest_path.read_bytes()).hexdigest()}))
