"""Independent final referee 1: fresh MI-03 source, using exact dependency caches.
Does not run Linux Comparator, alter mathematical inputs, or assert human review.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,tempfile,time
project=Path(__file__).resolve().parents[2];repo=project.parents[2];out=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
git=lambda root,*a:subprocess.check_output(['git','-C',str(root),*a])
freeze_path=project/'reviews/proof-freeze.json';assert sha(freeze_path)=='fcff9e256a6425853b15def24260b419613a72d9122c0a5bedea4b4cd5f0fd1d';freeze=json.loads(freeze_path.read_text())
assert len(freeze['files'])==101 and len(freeze['source_files'])==8
for rel,r in freeze['files'].items():assert sha(project/rel)==r['sha256'] and (project/rel).stat().st_size==r['bytes'],rel
for rel,h in freeze['source_files'].items():
 assert sha(repo/rel)==h,rel
 assert (repo/rel).read_bytes()==git(repo,'show',freeze['source_commit']+':'+rel),rel
(out/'frozen-inputs-before.json').write_text(json.dumps(freeze,indent=2)+'\n')
manifest=json.loads((project/'lake-manifest.json').read_text());dependencies=[]
for package in manifest['packages']:
 d=project/'.lake/packages'/package['name'];actual=git(d,'rev-parse','HEAD').decode().strip();dirty=git(d,'status','--porcelain','--untracked-files=no').decode()
 assert actual==package['rev'] and not dirty,package['name']
 dependencies.append({'name':package['name'],'revision':actual,'tracked_source_clean':True,'compiled_build_cache_reused':True})
assert len(dependencies)==10
(out/'dependency-pins.json').write_text(json.dumps(dependencies,indent=2)+'\n')
base_env=os.environ.copy();base_env['PATH']='/Users/georgestepaniants/.elan/bin:'+base_env.get('PATH','')
lake='/Users/georgestepaniants/.elan/bin/lake'
lean_path=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=project,env=base_env,text=True).strip()
lean=subprocess.check_output([lake,'env','which','lean'],cwd=project,env=base_env,text=True).strip();version=subprocess.check_output([lean,'--version'],text=True).strip();assert '4.33.1' in version
prefix=Path(tempfile.mkdtemp(prefix='nla-mi03-independent-final-ref1-',dir='/tmp'))
paths=[];excluded=[]
for raw in lean_path.split(':'):
 if not raw:continue
 d=(Path(raw) if Path(raw).is_absolute() else project/raw).resolve()
 if d==(project/'.lake/build/lib/lean').resolve():excluded.append(str(d));continue
 assert '/.lake/packages/' in str(d) or '/.elan/toolchains/' in str(d),str(d)
 paths.append(str(d))
assert len(excluded)==1
base_env['LEAN_PATH']=':'.join([str(prefix),*paths]);assert str((project/'.lake/build/lib/lean').resolve()) not in base_env['LEAN_PATH']
(out/'fresh-environment.json').write_text(json.dumps({'scope':'local macOS independent source elaboration; exact dependency cache reuse; Linux Comparator pending','lean':lean,'version':version,'prefix':str(prefix),'LEAN_PATH':base_env['LEAN_PATH'],'excluded_old_project_paths':excluded},indent=2)+'\n')
modules=['NLA.MI03.Definitions','NLA.MI03.Modulus','NLA.MI03.UpperBound','NLA.MI03.Roots','NLA.MI03.Witness','NLA.MI03.Sharpness','NLA.MI03.Proof','Solution','Challenge']
records=[];axioms=[]
for module in modules:
 source=module.replace('.','/')+'.lean';target=prefix/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
 args=[lean,'-o',str(target),source];t=time.monotonic();r=subprocess.run(args,cwd=project,env=base_env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log=out/(module.replace('.','-')+'.log');log.write_bytes(r.stdout)
 item={'module':module,'command':args,'exit_code':r.returncode,'elapsed_seconds':round(time.monotonic()-t,3),'source_sha256':sha(project/source),'object_sha256':sha(target) if target.exists() else None,'log_sha256':sha(log)};records.append(item)
 (out/'fresh-execution.json').write_text(json.dumps(records,indent=2)+'\n');print(module,'exit',r.returncode,flush=True)
 assert r.returncode==0,r.stdout.decode()
 text=r.stdout.decode();assert 'error:' not in text
 if module=='Challenge':assert text.count('declaration uses `sorry`')==8 and text.count('warning:')==8
 else:assert 'warning:' not in text
 for name,raw in re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]",text):
  found=[v.strip() for v in raw.split(',') if v.strip()];assert found==['propext','Classical.choice','Quot.sound'],(name,found);axioms.append({'declaration':name,'axioms':found})
assert len(axioms)==16
for rel,r in freeze['files'].items():assert sha(project/rel)==r['sha256'],rel
for rel,h in freeze['source_files'].items():assert sha(repo/rel)==h,rel
(out/'axioms.json').write_text(json.dumps({'result':'PASS','count':len(axioms),'records':axioms},indent=2)+'\n')
(out/'fresh-result.json').write_text(json.dumps({'result':'PASS','commands':len(records),'implementation_public_kernel_axiom_reports':len(axioms),'isolated_Challenge_placeholders':8,'all_101_frozen_inputs_unchanged':True,'all_8_original_sources_unchanged':True},indent=2)+'\n')
