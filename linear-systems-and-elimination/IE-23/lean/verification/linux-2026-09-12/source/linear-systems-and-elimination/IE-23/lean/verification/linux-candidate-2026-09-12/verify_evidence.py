"""Verify the complete candidate evidence and both current metadata wrappers offline."""
from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent
project=root.parents[1]
outer=root/'EVIDENCE-MANIFEST.json'
manifest=json.loads(outer.read_text())
actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and p!=outer}
assert actual==set(manifest['files']) and len(actual)==manifest['file_count']
def check(path,record):
    assert path.stat().st_size==record['bytes'],str(path)
    assert hashlib.sha256(path.read_bytes()).hexdigest()==record['sha256'],str(path)
for name,record in manifest['files'].items():check(root/name,record)
assert set(manifest['current_metadata_relative_to_project'])=={'README.md','formalization.yaml'}
for name,record in manifest['current_metadata_relative_to_project'].items():check(project/name,record)
print(json.dumps({'result':'PASS','bound_evidence_files':len(actual),'evidence_files_including_outer':len(actual)+1,
                  'bound_current_metadata_files':2,'outer_sha256':hashlib.sha256(outer.read_bytes()).hexdigest()}))
