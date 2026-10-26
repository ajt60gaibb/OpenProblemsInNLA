#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,platform,re,subprocess
here=Path(__file__).resolve().parent;repo=here.parents[5];root=repo/'lean-statements'
lean=repo.parent/'tooling/lean-4.33.1-darwin_aarch64/bin/lean'
objects=here/'objects';sources=here/'sources';objects.mkdir(parents=True,exist_ok=True)
assert not list(objects.rglob('*.olean')), 'Author replay requires fresh private outputs.'
lock=json.loads((here/'source-lock.json').read_text())
paths=[objects]+[p/'.lake/build/lib/lean'for p in sorted((root/'.lake/packages').iterdir())if(p/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,PATH=str(lean.parent)+os.pathsep+os.environ['PATH'],LEAN_PATH=os.pathsep.join(map(str,paths)))
commands=[]
for x in lock:
 rel=Path(x['path']).relative_to('lean-statements');src=sources/rel
 assert hashlib.sha256(src.read_bytes()).hexdigest()==x['sha256']
 assert hashlib.sha256((root/rel).read_bytes()).hexdigest()==x['sha256']
 obj=objects/rel.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 p=subprocess.run([str(lean),'-o',str(obj),str(rel)],cwd=sources,env=env,text=True,capture_output=True)
 log=here/(rel.stem+'.log');log.write_text(p.stdout+p.stderr)
 commands.append({'path':x['path'],'exit_code':p.returncode,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()})
 print(rel.stem,p.returncode,flush=True)
 if p.returncode:print(p.stdout+p.stderr);break
status='PASS'if len(commands)==5 and all(x['exit_code']==0 for x in commands)else'FAIL'
result={'status':status,'scope':'Fresh author replay of five recovered frozen sources; not independent review, full TR06 Target, Linux CI or Comparator evidence.','platform':platform.platform(),'lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'sources':lock,'commands':commands,'project_objects_reused':False}
(here/'result.json').write_text(json.dumps(result,indent=2)+'\n')
raise SystemExit(0 if status=='PASS'else 1)
