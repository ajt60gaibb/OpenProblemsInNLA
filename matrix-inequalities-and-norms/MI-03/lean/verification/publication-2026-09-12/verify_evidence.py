"""Check the exact sealed publication inventory offline, including nested manifests."""
from pathlib import Path
import hashlib, json
root = Path(__file__).resolve().parent
outer = root/'EVIDENCE-MANIFEST.json'
manifest = json.loads(outer.read_text())
actual = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and p != outer}
assert actual == set(manifest['files']) and len(actual) == manifest['file_count']
for name, record in manifest['files'].items():
    p = root/name
    assert p.stat().st_size == record['bytes'], name
    assert hashlib.sha256(p.read_bytes()).hexdigest() == record['sha256'], name
print(json.dumps({'result':'PASS','bound_files':len(actual),'total_files_including_outer':len(actual)+1,
                  'outer_sha256':hashlib.sha256(outer.read_bytes()).hexdigest()}))
