#!/usr/bin/env python3
"""Fresh author replay of exact Gaussian quadratic means/covariance/variance; no Target claim."""
import argparse,datetime,hashlib,json,os,pathlib,re,shutil,subprocess
B=pathlib.Path(__file__).resolve().parent;R=B.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=argparse.ArgumentParser(description=__doc__)
for key in ['lean-bin','package-cache','output']:p.add_argument('--'+key,type=pathlib.Path,required=True)
a=p.parse_args();a.lean_bin=a.lean_bin.resolve();a.package_cache=a.package_cache.resolve()
assert sha(a.lean_bin/'lean')=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
D=a.output.resolve();assert not D.exists();D.mkdir(parents=True);S=D/'sources';O=D/'objects';S.mkdir();O.mkdir()
def save(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
manifest=json.loads((R/'lean-statements/lake-manifest.json').read_text())
def pins():
 out=[]
 for dep in manifest['packages']:
  cache=a.package_cache/dep['name'];rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=cache,text=True).strip();clean=not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=cache,text=True).strip()
  assert rev==dep['rev'] and clean,dep['name'];out.append({'name':dep['name'],'revision':rev,'clean':clean,'library_available':(cache/'.lake/build/lib/lean').is_dir()})
 assert len(out)==10;return out
inputlock=B/'attained-input-lock.json';original=json.loads(inputlock.read_text())
def originals():
 out=[]
 for rec in original['source_inputs']:
  actual=sha(R/rec['path']);assert actual==rec['sha256'],rec['path'];out.append({'path':rec['path'],'sha256':actual})
 assert len(out)==18;return out
freeze_path=B/'GAUSSIAN_QUADRATIC_FREEZE_2026-10-26.json';freeze=json.loads(freeze_path.read_text())
for x in freeze['new_sources']+freeze['prerequisites']:assert sha(R/x['path'])==x['sha256']
ordered=[];seen=set();active=set()
def visit(m):
 if m in seen:return
 assert m not in active;active.add(m);local=pathlib.Path(m.replace('.','/')+'.lean');src=R/'lean-statements'/local
 for n in re.findall(r'^import\s+([\w.]+)\s*$',src.read_text(),re.M):
  if n.startswith(('NLA.','Reviewed.')):visit(n)
 dest=S/local;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(src.read_bytes());active.remove(m);seen.add(m);ordered.append({'module':m,'path':str(src.relative_to(R)),'sha256':sha(src)})
for m in ['NLA.Proofs.RE05.GaussianQuadraticCovariance','Reviewed.RE05']:visit(m)
consumer=B/'GaussianQuadraticConsumer.lean.txt';negative=B/'GaussianQuadraticNegative.lean.txt'
assert sha(consumer)==freeze['consumer_sha256'] and sha(negative)==freeze['negative_sha256']
(S/'Consumer.lean').write_bytes(consumer.read_bytes());(S/'Negative.lean').write_bytes(negative.read_bytes())
prepins=pins();preoriginals=originals()
lock={'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'author':'/root','scope':freeze['scope'],'freeze_sha256':sha(freeze_path),'driver_sha256':sha(pathlib.Path(__file__)),'consumer_sha256':sha(consumer),'negative_sha256':sha(negative),'source_closure':ordered,'pins_before':prepins,'original18_before':preoriginals,'project_objects_reused':False,'pinned_external_objects_reused':True};save(D/'source-lock.json',lock)
paths=[O]+[q/'.lake/build/lib/lean' for q in sorted(a.package_cache.iterdir()) if (q/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,PATH=str(a.lean_bin)+os.pathsep+os.environ['PATH'],LEAN_PATH=os.pathsep.join(map(str,paths)))
commands=[];passed=True
for idx,rec in enumerate(ordered+[{'module':'Consumer','source':'Consumer.lean'},{'module':'Negative','source':'Negative.lean'}]):
 local=pathlib.Path(rec.get('source',rec['module'].replace('.','/')+'.lean'));cmd=[str(a.lean_bin/'lean')]
 if rec['module'] not in ['Consumer','Negative']:
  obj=O/local.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);cmd+=['-o',str(obj)]
 cmd.append(str(local));log=D/('command-%02d.log'%idx)
 with log.open('w') as handle:run=subprocess.run(cmd,cwd=S,env=env,stdout=handle,stderr=subprocess.STDOUT)
 expected=1 if rec['module']=='Negative' else 0;commands.append({'module':rec['module'],'command':cmd,'exit_code':run.returncode,'expected_exit_code':expected,'log':log.name,'log_sha256':sha(log)});print(rec['module'],run.returncode,flush=True)
 if run.returncode!=expected:passed=False;break
std3=False;negative_rejected=False
if len(commands)==len(ordered)+2 and passed:
 positive=(D/commands[-2]['log']).read_text();reports=re.findall(r"'NLA.Proofs.RE05.([^']+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",positive)
 expected_names={n for x in freeze['new_sources'] for n in x['declarations']}
 assert {n for n,_,_ in reports}==expected_names and len(reports)==19,reports
 std3=all({v.strip() for v in xs.split(',') if v.strip()}<={'propext','Classical.choice','Quot.sound'} for n,word,xs in reports)
 neg=(D/commands[-1]['log']).read_text();negative_rejected='depends on sorry or unrecognized axioms' in neg and 'sorryAx' in neg and neg.count('error:')==1
 passed=std3 and negative_rejected
postpins=pins();postoriginals=originals();assert prepins==postpins and preoriginals==postoriginals
for x in ordered:assert sha(R/x['path'])==x['sha256'] and sha(S/(x['module'].replace('.','/')+'.lean'))==x['sha256']
assert sha(consumer)==freeze['consumer_sha256'] and sha(negative)==freeze['negative_sha256']
shutil.rmtree(O)
result={'passed':passed,'scope':freeze['scope'],'source_lock_sha256':sha(D/'source-lock.json'),'source_modules_fresh':len(ordered),'kernel_commands':len(commands),'commands':commands,'project_objects_reused':False,'private_objects_removed':not O.exists(),'pinned_external_objects_reused':True,'only_standard_three_axioms':std3,'expected_sorry_control_rejected':negative_rejected,'consumer_kernel_assertions':19,'literal_theorem_types':17,'additional_examples':5,'original18_before':preoriginals,'original18_after':postoriginals,'pins_before':prepins,'pins_after':postpins,'compiler':subprocess.check_output([str(a.lean_bin/'lean'),'--version'],text=True).strip(),'compiler_binary_sha256':sha(a.lean_bin/'lean'),'full_RE05_Target_proved':False,'probability_success_proved':False,'Linux_or_Comparator_acceptance':False};save(D/'result.json',result);print(json.dumps({k:v for k,v in result.items() if k not in ['commands','pins_before','pins_after','original18_before','original18_after']},indent=2));raise SystemExit(0 if passed else 1)
