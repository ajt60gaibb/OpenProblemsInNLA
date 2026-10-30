#!/usr/bin/env python3
"""Fresh author replay of the deterministic literal RE05 asymptotic bridge.
Only pinned external package objects are reused. Output must not already exist.
"""
import argparse,datetime,hashlib,json,os,pathlib,re,subprocess
B=pathlib.Path(__file__).resolve().parent
R=B.parents[5]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--lean-bin',type=pathlib.Path,required=True)
p.add_argument('--package-cache',type=pathlib.Path,required=True)
p.add_argument('--output',type=pathlib.Path,required=True)
a=p.parse_args();D=a.output.resolve();assert not D.exists();D.mkdir(parents=True)
S=D/'sources';O=D/'objects';S.mkdir();O.mkdir()
freeze_path=B/'SOURCE_FREEZE.json';freeze=json.loads(freeze_path.read_text())
assert sha(B/'INPUT_LOCK.json')==freeze['input_lock_sha256']
assert sha(pathlib.Path(__file__))==freeze['driver_sha256']
consumer=B/'Consumer.lean.txt';assert sha(consumer)==freeze['consumer_sha256']
inputlock=json.loads((B/'INPUT_LOCK.json').read_text())
def preserved():
 for x in inputlock['original_inputs']:assert sha(R/x['path'])==x['sha256'],x['path']
 for x in freeze['new_sources']:assert sha(R/x['path'])==x['sha256'],x['path']
 trpath=R/inputlock['TR04_final_freeze']['path']
 assert sha(trpath)==inputlock['TR04_final_freeze']['sha256']
 tr=json.loads(trpath.read_text());assert len(tr['inputs'])==205
 for rel,h in tr['inputs'].items():assert sha(R/tr['project']/rel)==h,rel
preserved()
manifest=json.loads((R/'lean-statements/lake-manifest.json').read_text());pins=[]
for dep in manifest['packages']:
 cache=a.package_cache.resolve()/dep['name']
 rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=cache,text=True).strip()
 clean=not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=cache,text=True).strip()
 assert rev==dep['rev'] and clean,dep['name']
 pins.append({'name':dep['name'],'revision':rev,'clean':clean})
ordered=[];seen=set();stack=set()
def visit(module):
 if module in seen:return
 assert module not in stack;stack.add(module)
 rel=pathlib.Path(module.replace('.','/')+'.lean');src=R/'lean-statements'/rel
 for dep in re.findall(r'^import\s+([\w.]+)\s*$',src.read_text(),re.M):
  if dep.startswith(('NLA.','Reviewed.')):visit(dep)
 dest=S/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(src.read_bytes())
 stack.remove(module);seen.add(module)
 ordered.append({'module':module,'path':str(src.relative_to(R)),'sha256':sha(src)})
for module in ['NLA.Proofs.RE05.QueryAsymptotic','Reviewed.RE05']:visit(module)
assert len(ordered)==7
assert not re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',(R/'lean-statements/NLA/Proofs/RE05/QueryAsymptotic.lean').read_text())
(S/'Consumer.lean').write_bytes(consumer.read_bytes())
scope='Deterministic literal SourceQueryBound implies QueryBound with fixed C=1000000,a=1,b=1; only 0<epsilon<1/2 and actual source-bound gate. No unconditional query/spectral charge/probability/OriginalClaim/SourceCompanion/Target/CI/Comparator claim.'
lock={'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'author':'/root/recover_algebra','scope':scope,'freeze_sha256':sha(freeze_path),'input_lock_sha256':sha(B/'INPUT_LOCK.json'),'driver_sha256':sha(pathlib.Path(__file__)),'consumer_sha256':sha(consumer),'source_closure':ordered,'pinned_dependencies':pins,'project_objects_reused':False,'external_pinned_package_objects_reused':True}
(D/'source-lock.json').write_text(json.dumps(lock,indent=2)+'\n')
paths=[O]+[p/'.lake/build/lib/lean' for p in sorted(a.package_cache.resolve().iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,PATH=str(a.lean_bin.resolve())+os.pathsep+os.environ['PATH'],LEAN_PATH=os.pathsep.join(map(str,paths)))
commands=[];passed=True
with (D/'build.log').open('w') as log:
 for x in ordered:
  rel=pathlib.Path(x['module'].replace('.','/')+'.lean');obj=O/rel.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(a.lean_bin.resolve()/'lean'),'-o',str(obj),str(rel)]
  run=subprocess.run(cmd,cwd=S,env=env,stdout=log,stderr=subprocess.STDOUT)
  commands.append({'module':x['module'],'exit_code':run.returncode});print(x['module'],run.returncode,flush=True)
  if run.returncode:passed=False;break
if passed:
 with (D/'consumer.log').open('w') as log:
  run=subprocess.run([str(a.lean_bin.resolve()/'lean'),'Consumer.lean'],cwd=S,env=env,stdout=log,stderr=subprocess.STDOUT)
 commands.append({'module':'Consumer','exit_code':run.returncode});passed=run.returncode==0
if passed:
 text=(D/'consumer.log').read_text()
 names=['sourceQueryBound_numeric','queryBound_of_sourceQueryBound']
 reports=re.findall(r"'NLA.Proofs.RE05.([^']+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",text)
 assert len(reports)==2 and {x[0] for x in reports}==set(names),reports
 for name,word,axioms in reports:assert {x.strip() for x in axioms.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'},(name,axioms)
 assert re.findall(r'AUDITED_THEOREM NLA.Proofs.RE05.(\w+)',text)==names,text
 assert not re.search(r'\b(sorryAx|Lean.ofReduceBool|error:)\b',text),text
for x in ordered:
 assert sha(R/x['path'])==x['sha256']
 assert sha(S/(x['module'].replace('.','/')+'.lean'))==x['sha256']
preserved()
result={'passed':passed,'scope':scope,'source_lock_sha256':sha(D/'source-lock.json'),'source_modules_fresh':len(ordered),'kernel_commands':len(commands),'commands':commands,'project_objects_reused':False,'external_pinned_package_objects_reused':True,'only_standard_three_axioms':True if passed else None,'actual_theorem_kind_checks':2 if passed else 0,'kernel_trust_assertions':2 if passed else 0,'literal_endpoint_examples':4,'original_inputs_unchanged':len(inputlock['original_inputs']),'TR04_canonical_inputs_unchanged':205,'compiler':subprocess.check_output([str(a.lean_bin.resolve()/'lean'),'--version'],text=True).strip(),'compiler_binary_sha256':sha(a.lean_bin.resolve()/'lean'),'logs':{f:sha(D/f) for f in ['build.log','consumer.log'] if (D/f).exists()}}
(D/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));raise SystemExit(0 if passed else 1)
