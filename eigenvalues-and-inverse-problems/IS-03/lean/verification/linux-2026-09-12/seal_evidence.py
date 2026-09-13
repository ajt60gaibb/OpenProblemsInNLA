"""Seal the complete IS-03 operational evidence; preserve every candidate input."""
from pathlib import Path
import json,hashlib,subprocess,datetime
O=Path(__file__).resolve().parent
C=json.loads((O/'audit-context.json').read_text())
P=Path(C['worktree'])/C['project']
def sha(b):return hashlib.sha256(b).hexdigest()
R=json.loads(next((O/'artifacts/lean-IS-03').glob('verify-*/result.json')).read_text())
assert len(R['input_sha256'])==303
assert subprocess.check_output(['git','-C',C['worktree'],'rev-parse','HEAD']).decode().strip()==C['commit']
for rel,digest in R['input_sha256'].items():
    assert sha((P/rel).read_bytes())==digest
    assert (O/'source'/C['project']/rel).read_bytes()==(P/rel).read_bytes()
for f in ['audit-checks.log','phase-checks.log']:
    assert 'PASS' in (O/f).read_text() and 'Traceback' not in (O/f).read_text()
outer=O/'EVIDENCE-MANIFEST.json'
files={str(f.relative_to(O)):{'sha256':sha(f.read_bytes()),'bytes':f.stat().st_size} for f in sorted(O.rglob('*')) if f.is_file() and f!=outer}
record={'result':'PASS independent actual Ubuntu operational review; coordinator acceptance/publication remain separate','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'run':C['run'],'candidate_commit':C['commit'],'project':C['project'],'reviewer':C['role'],'original_candidate_inputs_preserved':303,'file_count':len(files),'total_including_outer':len(files)+1,'exact_self_exclusion':'EVIDENCE-MANIFEST.json','inventory_scope':'All actual files recursively, including every nested file named EVIDENCE-MANIFEST.json and historical immutable source-snapshot manifests; only this exact outer file excluded.','nested_same_basename_manifests_included':sum(Path(r).name=='EVIDENCE-MANIFEST.json' for r in files),'operational_review_sha256':sha((O/'OPERATIONAL-REVIEW.md').read_bytes()),'files':files}
outer.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'verdict':'PASS','report_sha256':record['operational_review_sha256'],'outer_sha256':sha(outer.read_bytes()),'bound_files':len(files),'including_outer':len(files)+1,'nested_manifests':record['nested_same_basename_manifests_included'],'bytes':sum(v['bytes'] for v in files.values())+outer.stat().st_size},indent=2))
