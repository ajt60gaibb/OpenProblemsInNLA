#!/usr/bin/env python3
"""Independent frozen canonical package replay: all190 locals and selected exports/controls."""
import argparse,datetime,hashlib,json,os,pathlib,re,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent;REPO=HERE.parents[5]
PROJECT=REPO/'tensor-computations/TR-04/lean';TOOLING=REPO.parent/'tooling'
FREEZE=HERE.parent/'CANONICAL_PACKAGE_PREACCEPTANCE_FREEZE_2026-10-26.json'
EXPECT='8ee1d4585f3c0a60b101ec962fa9631ebbc043270cf35360669b8018152301eb'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert h(FREEZE)==EXPECT
freeze=json.loads(FREEZE.read_text())
a=argparse.ArgumentParser(description=__doc__);a.add_argument('--output',type=pathlib.Path,default=HERE/'final')
OUT=a.parse_args().output.resolve();SNAP=OUT/'sources';OBJECTS=OUT/'objects'
assert not OBJECTS.exists(),'No project object reuse is permitted; select an unused output.'
controls={'ProofConsumer':0,'IdentityConsumer':0,'ChallengeSupportPositive':0,'ChallengeTargetNegative':1,'SorryNegative':1}
control_records={n:dict(path=str((HERE/(n+'.lean')).relative_to(REPO)),sha256=h(HERE/(n+'.lean')),expected_exit_success=(e==0))for n,e in controls.items()}
original_lock=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-23/input-lock.json'
original=json.loads(original_lock.read_text())['records'];assert len(original)==25
archive_path=REPO/freeze['original_archive']['path'];assert h(archive_path)==freeze['original_archive']['sha256'];archive=json.loads(archive_path.read_text())
source_lock=json.loads((PROJECT/'proof-source-lock.json').read_text())
shared_manifest=json.loads((REPO/'lean-statements/lake-manifest.json').read_text())
canonical_manifest=json.loads((PROJECT/'lake-manifest.json').read_text())
pin_key=lambda x:(x['name'],x['rev'],x['url'],x.get('subDir'))
assert sorted(map(pin_key,shared_manifest['packages']))==sorted(map(pin_key,canonical_manifest['packages']))
CACHE=(REPO/'lean-statements/.lake/packages').resolve()
pin_receipts=[]
for item in canonical_manifest['packages']:
 actual=subprocess.check_output(['git','-C',str(CACHE/item['name']),'rev-parse','HEAD'],text=True).strip()
 assert actual==item['rev'],(item['name'],actual,item['rev'])
 pin_receipts.append(dict(name=item['name'],rev=actual,url=item['url']))
assert len(pin_receipts)==10

def check_inputs():
 assert h(FREEZE)==EXPECT
 for rel,sha in freeze['inputs'].items():assert h(PROJECT/rel)==sha,rel
 for item in source_lock['copies']:
  assert h(REPO/item['source'])==item['source_sha256']==h(REPO/item['destination']),item['module']
 for rec in original:assert h(REPO/rec['path'])==rec['sha256'],rec['path']
 for rec in archive['records']:
  assert h(REPO/rec['original_path'])==rec['sha256']==h(REPO/rec['archive_path']),rec['original_path']
 for rec in control_records.values():assert h(REPO/rec['path'])==rec['sha256']
check_inputs()
lean_files=sorted(p for p in PROJECT.rglob('*.lean')if '.lake'not in p.relative_to(PROJECT).parts)
assert len(lean_files)==190
local={str(p.relative_to(PROJECT).with_suffix('')).replace('/','.'):p for p in lean_files}
imports={m:re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',p.read_text(),re.M)for m,p in local.items()}
def closure(entry):
 seen=set()
 def visit(m):
  if m in seen:return
  seen.add(m)
  for d in imports[m]:
   if d in local:visit(d)
 visit(entry);return seen
assert not {'Challenge','FullChallenge'}&closure('FullSolution')
assert not {'Solution','FullSolution'}&closure('FullChallenge')
assert imports['FullChallenge']==['Challenge','NLA.Statements.TR04']
assert imports['FullSolution']==['Solution','NLA.Proofs.TR04.MachineTTFull','NLA.Proofs.TR04.MachineTTRecursiveChild']
for rel in freeze['inputs']:
 src=PROJECT/rel;dst=SNAP/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes())
(SNAP/'.lake').mkdir(exist_ok=True);(SNAP/'.lake/packages').symlink_to(CACHE,target_is_directory=True)
OBJECTS.mkdir(parents=True)
binary=TOOLING/'lean-4.33.1-darwin_aarch64/bin/lean'
paths=[OBJECTS]+[p/'.lake/build/lib/lean'for p in sorted(CACHE.iterdir())if(p/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,paths)),PATH=str(binary.parent)+os.pathsep+os.environ['PATH'])
ordered=[];active=set();seen=set()
def order(m):
 if m in seen:return
 assert m not in active,m
 active.add(m)
 for d in imports[m]:
  if d in local:order(d)
 active.remove(m);seen.add(m);ordered.append(m)
for m in sorted(local):order(m)
assert len(ordered)==190
inputs=dict(reviewer='/root/recover_geometry',scope='Independent canonical package/engine replay, with reviewer-authored mathematical prerequisites excluded from source approval; no Linux/Comparator/statuspromotion claim',freeze=dict(path=str(FREEZE.relative_to(REPO)),sha256=EXPECT),ordered_modules=ordered,package_input_count=205,ordinary_local_Lean_source_count=190,exact_shared_copies=184,TR04_proof_modules=179,package_snapshots={str(p.relative_to(PROJECT)):h(p)for p in lean_files},selected_exports=freeze['selected_exports'],controls=control_records,original_input_lock_sha256=h(original_lock),archive_manifest_sha256=h(archive_path),actual_dependency_revisions=pin_receipts,compiler_binary_sha256=h(binary),driver_sha256=h(pathlib.Path(__file__)))
(OUT/'replay-input-lock.json').write_text(json.dumps(inputs,indent=2)+'\n')
commands=[]
with (OUT/'source-build.log').open('w')as log:
 for m in ordered:
  rel=pathlib.Path(m.replace('.','/')+'.lean');dest=OBJECTS/rel.with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
  command=[str(binary),'-o',str(dest),str(SNAP/rel)];commands.append(command)
  log.write('MODULE '+m+'\n');log.flush()
  p=subprocess.run(command,cwd=SNAP,env=env,stdout=log,stderr=subprocess.STDOUT)
  log.write('EXIT '+m+' '+str(p.returncode)+'\n');log.flush();assert p.returncode==0,(m,OUT/'source-build.log')
control_results={}
for name,negative in controls.items():
 src=SNAP/(name+'.lean');src.write_bytes((HERE/(name+'.lean')).read_bytes())
 command=[str(binary),'-o',str(OBJECTS/(name+'.olean')),str(src)];commands.append(command)
 logpath=OUT/(name+'.log')
 with logpath.open('w')as log:p=subprocess.run(command,cwd=SNAP,env=env,stdout=log,stderr=subprocess.STDOUT)
 logs=logpath.read_text()
 if negative:
  assert p.returncode!=0 and '#assert_trust:'in logs and 'sorryAx'in logs,(name,p.returncode,logs)
 else:
  assert p.returncode==0 and 'sorryAx'not in logs,(name,p.returncode,logs)
  ax=re.findall(r'depends on axioms: \[([^]]*)\]',logs)
  assert all(set(x.strip()for x in s.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for s in ax)
 control_results[name]=dict(exit_code=p.returncode,expected_passed=True,expected_negative=bool(negative),log_sha256=h(logpath),printed_axioms=re.findall(r'depends on axioms: \[([^]]*)\]',logs))
check_inputs()
for rel,sha in freeze['inputs'].items():assert h(SNAP/rel)==sha,rel
result=dict(reviewer='/root/recover_geometry',executed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),passed=True,scope=inputs['scope'],frozen_package_sha256=EXPECT,replay_input_lock_sha256=h(OUT/'replay-input-lock.json'),driver_sha256=h(pathlib.Path(__file__)),ordinary_local_sources_fresh=190,total_kernel_invocations=len(commands),controls=control_results,all_selected_proofs_and_identity_positive=True,raw_challenge_placeholder_and_sorry_control_rejected=True,project_objects_reused=False,pinned_external_package_objects_reused=True,all205_frozen_package_inputs_and184_shared_copies_exact=True,all25_original_live_and_archive_records_exact=True,source_approval_excludes_reviewer_authored_prerequisites=True,independent_whole_mathematical_source_approval=False,authoritative_Linux_or_Comparator=False,canonical_status_promotion=False,compiler=subprocess.check_output([str(binary),'--version'],text=True).strip(),compiler_binary_sha256=h(binary),actual_dependency_revisions=pin_receipts,commands=commands,source_build_log_sha256=h(OUT/'source-build.log'))
(OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='commands'},indent=2))
