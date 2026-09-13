"""Implementation author's acknowledgement, checked before first proof edit."""
from pathlib import Path
import hashlib,json,subprocess,datetime
P=Path(__file__).resolve().parent.parent;W=P.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
gate=P/'verification/proof-start.json'
assert sha(gate)=='9070bf321c98230b8ada5ede4501710be5d2597dc820c8023c45900d8aef623b'
g=json.loads(gate.read_text());freeze=P/'reviews/statement-freeze.json'
assert sha(freeze)==g['statement_freeze_sha256']
f=json.loads(freeze.read_text())
for rel,h in f['files'].items():assert sha(P/rel)==h
for rel,h in f['source_files'].items():
 data=subprocess.check_output(['git','-C',str(W),'show','5830ed4fb06da0659414a3deb2a40ad327aca052:'+rel])
 assert hashlib.sha256(data).hexdigest()==h==sha(W/rel)
for rel,h in g['reports'].items():assert sha(P/rel)==h
for rel,r in g['evidence'].items():
 m=P/rel;assert sha(m)==r['sha256'];j=json.loads(m.read_text());assert len(j['files'])==r['bound_files']
 for sub,h in j['files'].items():
  q=m.parent/sub;assert sha(q)==h['sha256'] and q.stat().st_size==h['bytes']
assert not (P/'Solution.lean').exists()
existing=sorted(str(q.relative_to(P)) for q in (P/'NLA/MF16').glob('*.lean'))
assert existing==['NLA/MF16/Definitions.lean'],existing
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'author':'/root/leancert_examples','gate_sha256':sha(gate),'both_full_approvals_read':True,'approvals':g['reports'],'statement_freeze_sha256':sha(freeze),'project_files_checked':len(f['files']),'original_Git_sources_checked':len(f['source_files']),'implementation_files_before_first_edit':existing,'Solution_absent':True,'mathematical_statement_edits':False,'root_reserved_helper':'NLA/MF16/CayleyHamilton.lean; root becomes mathematical coauthor; final independent refs inventory and standards','result':'PASS; begin only the authorized complete nine-contract proof'}
(P/'verification/implementation-gate-acknowledged.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
