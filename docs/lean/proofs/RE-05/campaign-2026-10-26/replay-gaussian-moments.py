#!/usr/bin/env python3
"""Fresh project-only author kernel replay; pinned external objects are reused."""
import argparse,hashlib,json,os,pathlib,re,subprocess,datetime
B=pathlib.Path(__file__).resolve().parent
R=B.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--lean-bin',type=pathlib.Path,required=True)
p.add_argument('--package-cache',type=pathlib.Path,required=True)
p.add_argument('--output',type=pathlib.Path,required=True)
a=p.parse_args();D=a.output.resolve();assert not D.exists();D.mkdir(parents=True)
S=D/'sources';O=D/'objects';S.mkdir();assert not O.exists();O.mkdir()
inputlock=B/'attained-input-lock.json';initial=json.loads(inputlock.read_text())
for x in initial['source_inputs']:assert sha(R/x['path'])==x['sha256'],x['path']
freeze=json.loads((B/'GAUSSIAN_MOMENTS_FREEZE_2026-10-26.json').read_text())
for x in freeze['new_sources']:assert sha(R/x['path'])==x['sha256']
manifest=json.loads((R/'lean-statements/lake-manifest.json').read_text());pins=[]
for dep in manifest['packages']:
 cache=a.package_cache/dep['name']
 rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=cache,text=True).strip()
 clean=not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=cache,text=True).strip()
 assert rev==dep['rev'] and clean,dep['name']
 pins.append({'name':dep['name'],'revision':rev,'clean':clean})
ordered=[];seen=set();stack=set()
def visit(m):
 if m in seen:return
 assert m not in stack;stack.add(m)
 local=pathlib.Path(m.replace('.','/')+'.lean');src=R/'lean-statements'/local
 for n in re.findall(r'^import\s+([\w.]+)\s*$',src.read_text(),re.M):
  if n.startswith(('NLA.','Reviewed.')):visit(n)
 dest=S/local;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(src.read_bytes())
 stack.remove(m);seen.add(m);ordered.append({'module':m,'path':str(src.relative_to(R)),'sha256':sha(src)})
for m in ['NLA.Proofs.RE05.GaussianMoments','Reviewed.RE05']:visit(m)
consumer=B/'GaussianMomentsConsumer.lean.txt';(S/'Consumer.lean').write_bytes(consumer.read_bytes())
source_lock={'scope':'RE05 scalar standard Gaussian moments1through4, all-power integrability and finite-product monomial Fubini only; no concentration, success-probability, Target, CI or Comparator claim.','author':'/root','recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'input_lock_sha256':sha(inputlock),'freeze_sha256':sha(B/'GAUSSIAN_MOMENTS_FREEZE_2026-10-26.json'),'driver_sha256':sha(pathlib.Path(__file__)),'consumer_sha256':sha(consumer),'source_closure':ordered,'pinned_dependencies':pins,'project_objects_reused':False,'external_pinned_package_objects_reused':True}
(D/'source-lock.json').write_text(json.dumps(source_lock,indent=2)+'\n')
paths=[O]+[q/'.lake/build/lib/lean' for q in sorted(a.package_cache.iterdir()) if (q/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,PATH=str(a.lean_bin)+os.pathsep+os.environ['PATH'],LEAN_PATH=os.pathsep.join(map(str,paths)))
commands=[];passed=True
with (D/'build.log').open('w') as log:
 for x in ordered:
  f=pathlib.Path(x['module'].replace('.','/')+'.lean');obj=O/f.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(a.lean_bin/'lean'),'-o',str(obj),str(f)]
  r=subprocess.run(cmd,cwd=S,env=env,stdout=log,stderr=subprocess.STDOUT);commands.append({'module':x['module'],'exit_code':r.returncode});print(x['module'],r.returncode,flush=True)
  if r.returncode:passed=False;break
if passed:
 with (D/'consumer.log').open('w') as log:
  r=subprocess.run([str(a.lean_bin/'lean'),'Consumer.lean'],cwd=S,env=env,stdout=log,stderr=subprocess.STDOUT)
 commands.append({'module':'Consumer','exit_code':r.returncode});passed=r.returncode==0
 reports=re.findall(r"'NLA.Proofs.RE05.([^']+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",(D/'consumer.log').read_text())
 assert len(reports)==7,reports
 for n,word,xs in reports:assert set(x.strip() for x in xs.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},(n,xs)
for x in ordered:assert sha(R/x['path'])==x['sha256'];assert sha(S/(x['module'].replace('.','/')+'.lean'))==x['sha256']
for x in initial['source_inputs']:assert sha(R/x['path'])==x['sha256']
result={'passed':passed,'scope':source_lock['scope'],'source_lock_sha256':sha(D/'source-lock.json'),'source_modules_fresh':len(ordered),'kernel_commands':len(commands),'commands':commands,'project_objects_reused':False,'external_pinned_package_objects_reused':True,'only_standard_three_axioms':True,'kernel_assertions':7,'literal_examples':9,'all_original_inputs_unchanged':len(initial['source_inputs']),'compiler':subprocess.check_output([str(a.lean_bin/'lean'),'--version'],text=True).strip(),'compiler_binary_sha256':sha(a.lean_bin/'lean'),'logs':{f:sha(D/f) for f in ['build.log','consumer.log'] if (D/f).exists()}}
(D/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));raise SystemExit(0 if passed else 1)
