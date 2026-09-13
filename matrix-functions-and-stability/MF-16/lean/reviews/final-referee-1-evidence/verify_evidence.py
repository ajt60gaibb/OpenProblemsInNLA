from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent
target=E/'EVIDENCE-MANIFEST.json';m=json.loads(target.read_text())
assert m['inventory_rule']=='All internal files except only this exact outer manifest, plus the adjacent report. Nested manifests are included.'
internal={str(p.relative_to(E)) for p in E.rglob('*') if p.is_file() and p!=target}
expected=internal|{'../final-referee-1.md'}
assert set(m['files'])==expected and m['file_count']==len(expected) and m['internal_file_count']==len(internal)
for rel,r in m['files'].items():
 p=E/rel
 assert p.is_file() and not p.is_symlink()
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
 assert p.stat().st_size==r['bytes']
print(json.dumps({'result':'PASS','internal_files':len(internal),'bound_files':len(expected),
'outer_manifest_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
'report_sha256':m['files']['../final-referee-1.md']['sha256']}))
