"""Read-only verifier of this exact final referee2 evidence seal.
The sole internal exclusion is this directory's exact EVIDENCE-MANIFEST.json.
Use --frozen for the additional current mathematical-boundary audit before packaging.
"""
from pathlib import Path
import hashlib,json,sys,subprocess
E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
manifest=E/'EVIDENCE-MANIFEST.json';j=json.loads(manifest.read_text());rows=j['files']
for name,row in rows.items():
 f=E/name;assert sha(f)==row['sha256'] and f.stat().st_size==row['bytes'],name
actual={str(f.relative_to(E)) for f in E.rglob('*') if f.is_file() and f!=manifest}
assert actual=={x for x in rows if not x.startswith('../')}
assert j['internal_file_count']==len(actual) and j['file_count']==len(rows)
assert set(rows)-actual=={'../final-referee-2.md'}
f=json.loads((E/'proof-freeze.json.txt').read_text())
assert sha(E/'proof-freeze.json.txt')==j['proof_freeze_sha256']
assert sha(E/'statement-freeze.json.txt')==f['statement_freeze_sha256']
assert sha(E/'accepted-statement-gate.json.txt')==f['accepted_statement_gate_sha256']
audit=json.loads((E/'final-audit.json').read_text());assert audit['verdict']=='APPROVE'
for name,h in audit['evidence'].items():assert sha(E/name)==h,name
for rel in ['fresh-result.json','resume-result.json']:
 r=json.loads((E/rel).read_text())
 for row in r['commands']:
  assert sha(E/row['log'])==row['log_sha256'] and sha(E/row['source_snapshot'])==row['source_sha256']
assert json.loads((E/'resume-result.json').read_text())['prior_result_sha256']==sha(E/'fresh-result.json')
if '--frozen' in sys.argv:
 assert sha(P/'verification/proof-freeze.json')==j['proof_freeze_sha256']
 for name,h in f['files'].items():assert sha(P/name)==h,name
 for name,h in f['source_files'].items():
  raw=subprocess.check_output(['git','show',f['base']+':'+name],cwd=W)
  assert hashlib.sha256(raw).hexdigest()==h and (W/name).read_bytes()==raw,name
 for rel in f['nested_evidence_manifests_bound']:
  nf=P/rel;ns=json.loads(nf.read_text())['files']
  for name,row in ns.items():
   h=row if isinstance(row,str) else row['sha256'];target=nf.parent/name
   assert sha(target)==h,(rel,name)
   if isinstance(row,dict) and 'bytes' in row:assert target.stat().st_size==row['bytes']
  inside={str(f.relative_to(nf.parent)) for f in nf.parent.rglob('*') if f.is_file() and f!=nf}
  assert inside=={x for x in ns if not x.startswith('../')},rel
print(json.dumps({'verdict':'PASS','reviewer':'/root/mf16_final_referee','internal_files':len(actual),
 'bound_files':len(rows),'nested_prior_manifests':7,'current_frozen_boundary_checked':'--frozen' in sys.argv,
 'report_sha256':sha(P/'reviews/final-referee-2.md'),'evidence_manifest_sha256':sha(manifest)}))
