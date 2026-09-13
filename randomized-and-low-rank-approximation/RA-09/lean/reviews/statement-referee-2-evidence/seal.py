"""Seal only this review's evidence; preserve all frozen inputs unchanged."""
from pathlib import Path
import datetime,hashlib,json,subprocess
E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
f=json.loads((P/'reviews/statement-freeze.json').read_text())
assert sha(P/'reviews/statement-freeze.json')=='c144b68990fca06c554790b25bfaef7544c0a8baf532e5b38365fe74ee9c87ed'
for name,h in f['files'].items():assert sha(P/name)==h,name
for name,h in f['source_files'].items():
    raw=subprocess.check_output(['git','show',f['base']+':'+name],cwd=W)
    assert (W/name).read_bytes()==raw and sha(W/name)==h,name
assert not subprocess.check_output(['git','diff','--name-only'],cwd=W)
assert not (P/'Solution.lean').exists() and not list((P/'NLA').rglob('Proof.lean'))
fresh=json.loads((E/'fresh-result.json').read_text());assert fresh['verdict'].startswith('PASS')
assert len(fresh['commands'])==3 and all(x['exit_code']==0 for x in fresh['commands'])
for x in fresh['commands']:
    assert sha(P/x['source'])==x['source_sha256']
    assert sha(E/x['log'])==x['log_sha256']
assert json.loads((E/'exact-reconstruction.json').read_text())['verdict']=='PASS'
assert json.loads((E/'source-api-audit.json').read_text())['verdict']=='PASS'
report=P/'reviews/statement-referee-2.md'
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'reviewer':'/root/formal_review_standards','phase':'independent frozen statement referee 2',
 'verdict':'APPROVE','report_sha256':sha(report),'frozen_project_files_preserved':len(f['files']),
 'original_source_and_policy_files_preserved':len(f['source_files']),
 'no_proof_implementation_present':True,'no_frozen_or_tracked_edit':True,
 'prior_generic_design_authorship_disclosed':True}
(E/'seal-integrity.json').write_text(json.dumps(record,indent=2)+'\n')
outer=E/'EVIDENCE-MANIFEST.json'
files={str(q.relative_to(E)):{'bytes':q.stat().st_size,'sha256':sha(q)}
       for q in sorted(E.rglob('*')) if q.is_file() and q!=outer}
files['../statement-referee-2.md']={'bytes':report.stat().st_size,'sha256':sha(report)}
manifest={'phase':record['phase'],'reviewer':record['reviewer'],'files':files,
 'file_count':len(files),'self_exclusion':'Only this exact outer EVIDENCE-MANIFEST.json path; nested manifests are included.',
 'review_verdict':'APPROVE','mathematical_proof_or_Linux_verification_claimed':False}
outer.write_text(json.dumps(manifest,indent=2)+'\n')
for name,row in files.items():assert sha(E/name)==row['sha256'] and (E/name).stat().st_size==row['bytes']
print(json.dumps({'report_sha256':sha(report),'outer_sha256':sha(outer),
 'bound_files_including_report':len(files),'total_including_outer':len(files)+1},indent=2))
