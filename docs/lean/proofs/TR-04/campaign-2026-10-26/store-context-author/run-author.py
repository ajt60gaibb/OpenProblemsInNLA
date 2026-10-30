#!/usr/bin/env python3
"""Fresh author replay of the literal fixed-program output storage and first context return."""
import hashlib,json,os,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent
PROJECT=HERE.parents[5]/'lean-statements'
TOOLING=HERE.parents[6]/'tooling'
SOURCES=HERE/'sources';OBJECTS=HERE/'objects';OBJECTS.mkdir(exist_ok=False)
CACHE=PROJECT/'.lake/packages'
ENV=dict(os.environ,PATH=str(TOOLING/'lean-4.33.1-darwin_aarch64/bin')+os.pathsep+os.environ['PATH'],LEAN_PATH=os.pathsep.join(map(str,[OBJECTS]+[p/'.lake/build/lib/lean' for p in sorted(CACHE.iterdir()) if (p/'.lake/build/lib/lean').is_dir()])))
(SOURCES/'ExactConsumer.lean').write_bytes((HERE/'ExactConsumer.lean').read_bytes())
lock=json.loads((HERE/'source-lock.json').read_text());commands=[]
assert len(lock['sources'])==160
for rec in lock['runtime_pins']:
 assert hashlib.sha256((PROJECT/rec['path']).read_bytes()).hexdigest()==rec['sha256']
with (HERE/'build.log').open('w') as log:
 for rec in lock['sources']+[{'path':'ExactConsumer.lean','sha256':hashlib.sha256((HERE/'ExactConsumer.lean').read_bytes()).hexdigest()}]:
  rel=pathlib.Path(rec['path']);src=SOURCES/rel
  assert hashlib.sha256(src.read_bytes()).hexdigest()==rec['sha256']
  dst=OBJECTS/rel.with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(TOOLING/'lean-4.33.1-darwin_aarch64/bin/lean'),'-o',str(dst),str(src)]
  proc=subprocess.run(cmd,cwd=SOURCES,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log.write(proc.stdout);log.flush();commands.append({'path':str(src),'sha256':rec['sha256'],'command':cmd,'exit_code':proc.returncode,'output':proc.stdout})
  print(rec['path'],proc.returncode,flush=True)
  if proc.returncode:break
import re
axiom_lists=re.findall(r'depends on axioms: \[([^]]*)\]', (HERE/'build.log').read_text())
assert axiom_lists and all(set(x.strip() for x in a.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'} for a in axiom_lists)
assert 'sorryAx' not in (HERE/'build.log').read_text()
for rec in lock['sources']:
 assert hashlib.sha256((PROJECT/rec['path']).read_bytes()).hexdigest()==rec['sha256']
result={'compiler':subprocess.run([str(TOOLING/'lean-4.33.1-darwin_aarch64/bin/lean'),'--version'],text=True,capture_output=True,check=True).stdout.strip(),'kernel_assertion_count':6,'source_lock_sha256':hashlib.sha256((HERE/'source-lock.json').read_bytes()).hexdigest(),'printed_axiom_lists':axiom_lists,'external_pinned_package_objects_reused':True,'project_objects_reused':False,'scope':'Author kernel replay, not independent review, full TR04 Target, Linux CI, or Comparator evidence','success':len(commands)==161 and all(x['exit_code']==0 for x in commands),'fresh_source_commands':len(commands),'commands':commands}
(HERE/'result.json').write_text(json.dumps(result,indent=2)+'\n')
raise SystemExit(0 if result['success'] else 1)
