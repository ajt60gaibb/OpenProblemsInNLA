#!/usr/bin/env python3
"""Independent fresh RE05 minimizer/chosenSVD prerequisite and literal boundary checks."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,sys
HERE=Path(__file__).resolve().parent;REPO=HERE.parents[5];LIVE=REPO/'lean-statements';OUT=HERE/'final';SNAP=OUT/'sources';OBJECTS=OUT/'objects';TOOL=REPO.parent/'tooling';FREEZE=HERE.parent/'PREREQUISITES_FREEZE_2026-10-26.json'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();expected='88984167fdfc6637abf090b62811c10211f189204587c3b654fbc57e8660582f'
assert h(FREEZE)==expected
f=json.loads(FREEZE.read_text());orig=HERE.parent/'attained-input-lock.json';assert h(orig)==f['attained_input_lock_sha256'];inp=json.loads(orig.read_text());consumer_sha=h(HERE/'Consumer.lean')
seen=set();records=[]
def visit(m):
 if m in seen:return
 seen.add(m);p=LIVE/(m.replace('.','/')+'.lean')
 for d in re.findall(r'^import\s+(\S+)\s*$',p.read_text(),re.M):
  if d.startswith(('NLA.','Reviewed.')):visit(d)
 records.append(dict(module=m,path=str(p.relative_to(REPO)),sha256=h(p)))
for m in ['NLA.Proofs.RE05.Attained','NLA.Proofs.RE05.SVDTotal','Reviewed.RE05']:visit(m)
def check():
 assert h(FREEZE)==expected and h(orig)==f['attained_input_lock_sha256'] and h(HERE/'Consumer.lean')==consumer_sha
 for r in inp['source_inputs']+f['new_sources']+records:assert h(REPO/r['path'])==r['sha256'],r['path']
check();assert not OBJECTS.exists(),'Fresh output required; no project object reuse.'
for r in records:
 p=SNAP/Path(r['path']).relative_to('lean-statements');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((REPO/r['path']).read_bytes())
(SNAP/'.lake').mkdir(exist_ok=True);CACHE=(LIVE/'.lake/packages').resolve();(SNAP/'.lake/packages').symlink_to(CACHE,target_is_directory=True)
binary=TOOL/'lean-4.33.1-darwin_aarch64/bin/lean';paths=[OBJECTS]+[p/'.lake/build/lib/lean'for p in sorted(CACHE.iterdir())if(p/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,paths)),PATH=str(binary.parent)+os.pathsep+os.environ['PATH']);commands=[]
lock=dict(reviewer='/root/recover_geometry',scope='Independent RE05 newtwo-source/math-interface review and fresh prerequisite replay; earlier SVD mathematics excluded; no full success/query/Target/CI/Comparator claim',freeze=dict(path=str(FREEZE.relative_to(REPO)),sha256=expected),source_inputs=inp['source_inputs'],new_sources=f['new_sources'],fresh_project_closure=records,consumer_sha256=consumer_sha,driver_sha256=h(Path(__file__)))
(OUT/'source-lock.json').write_text(json.dumps(lock,indent=2)+'\n')
with (OUT/'source-build.log').open('w')as log:
 for r in records:
  rel=Path(r['path']).relative_to('lean-statements');dst=OBJECTS/rel.with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(binary),'-o',str(dst),str(SNAP/rel)];commands.append(cmd);p=subprocess.run(cmd,cwd=SNAP,env=env,stdout=log,stderr=subprocess.STDOUT);log.write(r['module']+' EXIT '+str(p.returncode)+'\n');log.flush();assert p.returncode==0,r['module']
src=SNAP/'Consumer.lean';src.write_bytes((HERE/'Consumer.lean').read_bytes());cmd=[str(binary),'-o',str(OBJECTS/'Consumer.olean'),str(src)];commands.append(cmd)
with (OUT/'consumer-build.log').open('w')as log:p=subprocess.run(cmd,cwd=SNAP,env=env,stdout=log,stderr=subprocess.STDOUT)
assert p.returncode==0,OUT/'consumer-build.log'
logs=(OUT/'source-build.log').read_text()+(OUT/'consumer-build.log').read_text();assert 'sorryAx'not in logs
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',logs);assert all(set(x.strip()for x in a.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for a in axioms)
check()
for r in records:assert h(SNAP/Path(r['path']).relative_to('lean-statements'))==r['sha256']
res=dict(reviewer='/root/recover_geometry',executed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),passed=True,scope=lock['scope'],source_lock_sha256=h(OUT/'source-lock.json'),freeze_sha256=expected,new_sources=2,fresh_project_sources=len(records),kernel_commands=len(commands),explicit_kernel_consumer_assertions=14,project_objects_reused=False,pinned_external_package_objects_reused=True,all_original_model_review_registry_pins_and_new_sources_exact=True,standard_axioms_only=True,literal_attained_and_actual_exactSVD_checked=True,empty_matrix_dependent_zero_family_exact_zero_residual_checked=True,preserved_reviewed_full_target_identity_only=True,full_RE05_Target_proved=False,source_approval_excludes_earlier_authored_SVD_prerequisites=True,compiler=subprocess.check_output([str(binary),'--version'],text=True).strip(),compiler_binary_sha256=h(binary),commands=commands,evidence=[dict(path=str(p.relative_to(OUT)),sha256=h(p))for p in [OUT/'source-build.log',OUT/'consumer-build.log',src]])
(OUT/'result.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
