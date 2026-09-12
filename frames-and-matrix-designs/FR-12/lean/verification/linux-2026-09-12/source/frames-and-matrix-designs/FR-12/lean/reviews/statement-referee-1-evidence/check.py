#!/usr/bin/env python3
"""Independent statement-only source review. No proof implementation is introduced."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, time, re
project=Path(__file__).resolve().parents[2]
repo=project.parents[2]
evidence=Path(__file__).resolve().parent
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
freeze_path=project/'reviews/statement-freeze.json'
freeze_sha='5fbbcbce16da324a186dd765d120c883e4800efe2e491fbf069c9f7c74f5372c'
assert sha(freeze_path)==freeze_sha
freeze=json.loads(freeze_path.read_text())
assert not (project/'Solution.lean').exists()
assert sorted(str(p.relative_to(project)) for p in (project/'NLA').rglob('*.lean')) == ['NLA/FR12/Definitions.lean']
for rel,h in freeze['files'].items(): assert sha(project/rel)==h,rel
for rel,h in freeze['source_files'].items():
    assert sha(repo/rel)==h,rel
    original=subprocess.check_output(['git','show',freeze['base_commit']+':'+rel],cwd=repo)
    assert hashlib.sha256(original).hexdigest()==h,rel
pins=[]
for package in json.loads((project/'lake-manifest.json').read_text())['packages']:
    local=project/'.lake/packages'/package['name']
    rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=local,text=True).strip()
    dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=local,text=True)
    assert rev==package['rev'] and not dirty,package['name']
    pins.append({'name':package['name'],'rev':rev,'tracked_sources_clean':True})
lake='/Users/georgestepaniants/.elan/bin/lake'
lean='/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean'
raw=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=project,text=True).strip()
prefix=Path('/tmp/nla-lean-formalization/referee-fr12-1/build')
prefix.mkdir(parents=True,exist_ok=True)
local_cache=(project/'.lake/build/lib/lean').resolve()
deps=[p for p in raw.split(os.pathsep) if p and Path(p).resolve()!=local_cache]
env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(prefix),*deps]))
results=[]
for module,src in [('NLA/FR12/Definitions',project/'NLA/FR12/Definitions.lean'),('Challenge',project/'Challenge.lean'),('Inspect',evidence/'Inspect.lean')]:
    out=prefix/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
    cmd=[lean,'-o',str(out),'-i',str(out.with_suffix('.ilean')),str(src)]
    log_path=evidence/(module.rsplit('/',1)[-1]+'.log')
    with log_path.open('w') as log:
        log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
        t=time.monotonic();proc=subprocess.run(cmd,cwd=project,env=env,stdout=log,stderr=subprocess.STDOUT)
    rec={'module':module,'source_sha256':sha(src),'exit_code':proc.returncode,'seconds':round(time.monotonic()-t,3),'log_sha256':sha(log_path)}
    results.append(rec);print(json.dumps(rec),flush=True)
    if proc.returncode: break
assert len(results)==3 and all(r['exit_code']==0 for r in results),results
clog=(evidence/'Challenge.log').read_text(); ilog=(evidence/'Inspect.log').read_text()
assert clog.count("declaration uses `sorry`")==7,clog
reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",ilog)
assert len(reports)==13,len(reports)
for name,ax in reports[:6]: assert set(re.sub(r'\.\{[^}]*\}', '', x.strip()) for x in ax.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},name
for name,ax in reports[6:]: assert 'sorryAx' in ax,name
for rel,h in freeze['files'].items(): assert sha(project/rel)==h,rel
for rel,h in freeze['source_files'].items(): assert sha(repo/rel)==h,rel
result={'status':'PASS: independent statement-only checks; no completed proof checked or claimed',
'review_date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
'freeze_sha256':freeze_sha,'frozen_candidate_files_unchanged':len(freeze['files']),
'original_source_files_match_exact_base_commit':len(freeze['source_files']),
'base_commit':freeze['base_commit'],'scope':'macOS source re-elaboration with pinned cached dependencies; no authoritative Linux check',
'project_cache_excluded':str(local_cache),'separate_output_prefix':str(prefix),'source_commands':results,
'intentional_challenge_holes':7,'definition_kernel_assertions':6,'definition_axioms_within_standard_three':True,
'all_seven_placeholder_axiom_reports_expose_sorryAx':True,'dependency_pins':pins}
(evidence/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print('RESULT '+sha(evidence/'result.json'),flush=True)
