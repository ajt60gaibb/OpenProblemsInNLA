"""Verify every retained operational-evidence file, including nested manifests."""
from pathlib import Path
import hashlib,json
out=Path(__file__).resolve().parent
outer=out/'EVIDENCE-MANIFEST.json'
manifest=json.loads(outer.read_text())
actual={p.relative_to(out).as_posix() for p in out.rglob('*') if p.is_file() and p!=outer}
assert actual==set(manifest['files']) and len(actual)==manifest['file_count']
for rel,record in manifest['files'].items():
    path=out/rel
    assert '..' not in Path(rel).parts and not Path(rel).is_absolute()
    assert path.is_file() and not path.is_symlink()
    assert path.stat().st_size==record['bytes'],rel
    assert hashlib.sha256(path.read_bytes()).hexdigest()==record['sha256'],rel
print(json.dumps({'result':'PASS','bound_files':len(actual),'total_files_including_outer_manifest':len(actual)+1,
                  'outer_manifest_sha256':hashlib.sha256(outer.read_bytes()).hexdigest()}))
