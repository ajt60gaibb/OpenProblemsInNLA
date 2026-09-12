"""Seal every independent review input/output, excluding only this outer manifest."""
from pathlib import Path
import datetime, hashlib, json
out = Path(__file__).resolve().parent
manifest = out/'EVIDENCE-MANIFEST.json'
files = {}
for p in sorted(out.rglob('*')):
    if p.is_file() and p != manifest:
        files[p.relative_to(out).as_posix()] = {
            'bytes':p.stat().st_size,
            'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
data = {'reviewer':'/root/leancert_examples','role':'IV-06 independent final proof referee 1',
    'created_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope':'All files in this review evidence folder, including archived auxiliary diagnostic failures. Only the outer EVIDENCE-MANIFEST.json itself is excluded.',
    'file_count':len(files),'files':files}
manifest.write_text(json.dumps(data,indent=2)+'\n')
for rel,entry in files.items():
    p=out/rel
    assert hashlib.sha256(p.read_bytes()).hexdigest()==entry['sha256']
    assert p.stat().st_size==entry['bytes']
print(json.dumps({'status':'PASS','files':len(files),'manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest()}))
