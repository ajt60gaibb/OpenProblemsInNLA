"""Seal all independent IS03 review evidence; exclude only the outer manifest."""
from pathlib import Path
import datetime,hashlib,json
out=Path(__file__).resolve().parent
manifest=out/'EVIDENCE-MANIFEST.json'
files={}
for path in sorted(out.rglob('*')):
    if path.is_file() and path != manifest:
        files[path.relative_to(out).as_posix()]={'bytes':path.stat().st_size,
            'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
manifest.write_text(json.dumps({'reviewer':'/root/leancert_examples',
    'role':'IS-03 independent statement referee 1',
    'created_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope':'Every file in this evidence folder, excluding only this outer EVIDENCE-MANIFEST.json itself.',
    'file_count':len(files),'files':files},indent=2)+'\n')
for rel,entry in files.items():
    path=out/rel
    assert path.stat().st_size==entry['bytes']
    assert hashlib.sha256(path.read_bytes()).hexdigest()==entry['sha256']
print(json.dumps({'status':'PASS','files':len(files),'manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest()}))
