"""Offline integrity verification for the exact independent IS-03 referee-2 evidence."""
from pathlib import Path
import hashlib,json
out=Path(__file__).resolve().parent
manifest_path=out/'EVIDENCE-MANIFEST.json'
d=json.loads(manifest_path.read_text())
assert d['self_exclusion_only']=='EVIDENCE-MANIFEST.json'
assert d['bound_file_count']==len(d['files'])
allowed_report=(out.parent/'proof-referee-2.md').resolve()
expected={str(p.relative_to(out)) for p in out.rglob('*') if p.is_file() and p!=manifest_path}
expected.add('../proof-referee-2.md')
assert set(d['files'])==expected,(set(d['files'])^expected)
for n,r in d['files'].items():
    p=(out/n).resolve();assert p.is_relative_to(out.resolve()) or p==allowed_report,n
    assert p.is_file() and not (out/n).is_symlink(),n
    b=p.read_bytes();assert len(b)==r['bytes'],n
    assert hashlib.sha256(b).hexdigest()==r['sha256'],n
print('PASS:',len(d['files']),'bound report/evidence files; only the exact outer manifest excludes itself')
