"""Seal the independent review's actual evidence, excluding only its own manifest."""
from pathlib import Path
import hashlib,json
OUT=Path(__file__).resolve().parent
PROJECT=OUT.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
f=json.loads((PROJECT/'verification/proof-freeze.json').read_text())
for rel,r in f['files'].items():assert sha(PROJECT/rel)==r['sha256'],rel
files={str(q.relative_to(OUT)):{'sha256':sha(q),'bytes':q.stat().st_size} for q in sorted(OUT.rglob('*')) if q.is_file() and q!=OUT/'EVIDENCE-MANIFEST.json'}
r=PROJECT/'reviews/proof-referee-1.md'
(OUT/'EVIDENCE-MANIFEST.json').write_text(json.dumps({'verdict':'PASS','reviewer':'/root/solved_statement_inventory','proof_freeze_sha256':sha(PROJECT/'verification/proof-freeze.json'),'report':{'file':'../proof-referee-1.md','sha256':sha(r),'bytes':r.stat().st_size},'files':files},indent=2)+'\n')
print('report',sha(r));print('manifest',sha(OUT/'EVIDENCE-MANIFEST.json'));print('retained files',len(files))
