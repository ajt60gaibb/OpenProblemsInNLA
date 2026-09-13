"""Remove only this referee's disposable objects after verifying their fresh hashes."""
from pathlib import Path
import datetime,hashlib,json
E=Path(__file__).resolve().parent
record=json.loads((E/'fresh-checks.json').read_text())
prefix=Path(record['fresh_prefix'])
assert prefix.parent.resolve()==Path('/tmp/nla-lean-formalization/independent-prefixes').resolve()
assert prefix.name.startswith('ra08-final-referee2-')
objects={rel:h for c in record['commands'][:18] for rel,h in c['fresh_objects'].items()}
assert len(objects)==36
actual={str(f.relative_to(prefix)) for f in prefix.rglob('*') if f.is_file()}
assert actual==set(objects)
removed={}
for rel,h in objects.items():
 p=prefix/rel
 assert not p.is_symlink() and p.suffix in ['.olean','.ilean']
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 removed[rel]={'sha256':h,'bytes':p.stat().st_size}
receipt={'phase':'planned and hash-verified','file_count':36,'prefix':str(prefix),
 'removed_files':removed,'bytes':sum(r['bytes'] for r in removed.values()),
 'dependency_or_other_agent_objects_touched':False}
out=E/'disposable-object-cleanup.json';out.write_text(json.dumps(receipt,indent=2)+'\n')
for rel in objects:(prefix/rel).unlink()
assert not any(p.is_file() for p in prefix.rglob('*'))
for d in sorted((p for p in prefix.rglob('*') if p.is_dir()),key=lambda p:len(p.parts),reverse=True):d.rmdir()
prefix.rmdir()
receipt.update(phase='completed',utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
out.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'result':'PASS','own_objects_removed':36,'bytes':receipt['bytes']}))
