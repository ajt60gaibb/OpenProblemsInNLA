"""Adapt actual-runtime checks to RA09; original partial metadata stays preserved."""
from pathlib import Path
import hashlib,json
O=Path(__file__).resolve().parent
S=Path('/tmp/nla-lean-ra08-worktree/randomized-and-low-rank-approximation/RA-08/lean/verification/linux-2026-09-12')
polls=[]
for p in (O/'polls').iterdir():
 r=json.loads((p/'run.json').read_text())
 if r['status']=='completed' and r['conclusion']=='success':polls.append(p)
assert polls
p=sorted(polls)[-1]
raw={'run':str((p/'run.json').relative_to(O)),'jobs':str((p/'jobs.json').relative_to(O)),'permanent-id-run':str((p/'permanent-id-run.json').relative_to(O))}
meta={'scope':'Original authenticated completed-run poll; earlier selected-job metadata remains unmodified and records its earlier in-progress state.','files':{k:{'path':n,'sha256':hashlib.sha256((O/n).read_bytes()).hexdigest()} for k,n in raw.items()}}
(O/'final-metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
f=(S/'fetch_final.py').read_text().replace("S=O/'retrieval/selected'\nrun=json.loads((S/'run.json').read_text())\njobs=json.loads((S/'jobs.json').read_text())","M=json.loads((O/'final-metadata.json').read_text())\nrun=json.loads((O/M['files']['run']['path']).read_text())\njobs=json.loads((O/M['files']['jobs']['path']).read_text())")
# Retain all whole-job source identities, without claiming new semantic review of inherited projects.
f=f.replace("for job in jobs['jobs']:\n        if job['name'] not in ['select','checker-controls'] and not job['name'].startswith(f\"verify ({C['problem']},\"):continue","for job in jobs['jobs']:")
f=f.replace("assert z.read(candidates[0])==(O/f\"job-{job['id']}.log\").read_bytes()","body=z.read(candidates[0]);assert C['commit'].encode() in body and b'##[error]' not in body\n        if (O/f\"job-{job['id']}.log\").exists():\n            assert body==(O/f\"job-{job['id']}.log\").read_bytes()")
f=f.replace("'selected_authenticated_job_logs_identical_to_original_archive_entries':associations","'all_actual_job_source_commit_and_success_log_associations':associations,\n 'selected_authenticated_job_logs_identical_to_original_archive_entries':{k:v for k,v in associations.items() if (O/f'job-{k}.log').exists()}")
(O/'fetch_final.py').write_text(f)
r=(S/'runtime_audit.py').read_text().replace('RA-08','RA-09').replace('RA08','RA09').replace('==613','==524').replace(':613',':524').replace('==14','==17').replace(':14',':17').replace('==59','==49').replace(' == 59',' == 49').replace(':59',':49').replace('(14 declarations)','(17 declarations)')
r=r.replace("['Definitions','Basis','Certificate','Fourth','Functional','Location','Numerical','OrderedExistence','Polynomial','ProjectionNorm','Proof','Scalar','Spectral','SpectralCFC','Tails','Witness']","['Definitions','ZeroColumn','Frobenius','Harmonic','Scalar','SpectralCFC','OrderedExistence','Spectral','Averaging','ZeroTail','Overlap','TailScale','OverlapOrder','Transfer','Proof']")
r=r.replace('build_jobs==[2710,3161]','build_jobs==[2710,2726]')
r=r.replace("run=json.loads((selected/'run.json').read_text())\nJ=json.loads((selected/'jobs.json').read_text());jobs=J['jobs']","F=json.loads((OUT/'final-metadata.json').read_text())\nfor info in F['files'].values():assert sha((OUT/info['path']).read_bytes())==info['sha256']\nrun=json.loads((OUT/F['files']['run']['path']).read_text())\nJ=json.loads((OUT/F['files']['jobs']['path']).read_text());jobs=J['jobs']")
r=r.replace("'complete_original_page_identity':True","'complete_original_page_identity':True,'scope':'Original selected-job retrieval snapshot; final all-job success comes from separately retained final-metadata.json'")
(O/'runtime_audit.py').write_text(r)
(O/'runtime-inspector-adaptation.json').write_text(json.dumps({'source_runtime':str(S/'runtime_audit.py'),'source_runtime_sha256':hashlib.sha256((S/'runtime_audit.py').read_bytes()).hexdigest(),'runtime_sha256':hashlib.sha256(r.encode()).hexdigest(),'source_fetch_final':str(S/'fetch_final.py'),'source_fetch_final_sha256':hashlib.sha256((S/'fetch_final.py').read_bytes()).hexdigest(),'fetch_final_sha256':hashlib.sha256(f.encode()).hexdigest(),'changes':'Actual RA09 524 inputs, 17 exports, 49 source trust reports, 15 modules and graph jobs 2710/2726. Completed raw poll supplies final all-job status without overwriting earlier partial selected metadata. Whole archive checks source commit/no CI errors for all 17 actual job logs. All control and sandbox checks retain actual expected failure reasons.'},indent=2)+'\n')
