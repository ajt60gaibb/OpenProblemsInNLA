"""Seal the candidate's metadata and retained integrity/validation artifacts."""
from pathlib import Path
import hashlib,json
OUT=Path(__file__).resolve().parent
PROJECT=OUT.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
i=json.loads((OUT/'integrity.json').read_text())
assert sha(PROJECT/'README.md')==i['current_README_sha256']
assert sha(PROJECT/'formalization.yaml')==i['formalization_yaml_sha256']
files={str(q.relative_to(OUT)):{'sha256':sha(q),'bytes':q.stat().st_size} for q in sorted(OUT.rglob('*')) if q.is_file() and q!=OUT/'EVIDENCE-MANIFEST.json'}
(OUT/'EVIDENCE-MANIFEST.json').write_text(json.dumps({'stage':'Reviewed local Linux candidate; actual Linux pending','proof_freeze_sha256':i['proof_freeze_sha256'],'metadata':{rel:{'sha256':sha(PROJECT/rel),'bytes':(PROJECT/rel).stat().st_size} for rel in ['README.md','formalization.yaml']},'files':files},indent=2)+'\n')
for rel in ['CANDIDATE-HANDOFF.md','integrity.json','EVIDENCE-MANIFEST.json']:
 print(rel,sha(OUT/rel))
print('candidate files',len(files))
