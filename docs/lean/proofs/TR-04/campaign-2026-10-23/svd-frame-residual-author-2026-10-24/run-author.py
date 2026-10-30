#!/usr/bin/env python3
"""Fresh two-bridge author replay; exact old twelve source-bound objects reused."""
import hashlib,json,os,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent
PROJECT=HERE.parents[5]/'lean-statements';TOOLING=HERE.parents[6]/'tooling'
SOURCES=HERE/'sources';OBJECTS=HERE/'objects';BASE=HERE.parent/'svd-eckart-author'
assert not OBJECTS.exists(), 'Use a new output directory or preserve the prior replay before rebuilding.'
OBJECTS.mkdir();lock=json.loads((HERE/'source-lock.json').read_text())
assert hashlib.sha256((BASE/'source-lock.json').read_bytes()).hexdigest()==lock['frozen_base_lock_sha256']
base_lock=json.loads((BASE/'source-lock.json').read_text());old_objects=[]
base_result=json.loads((BASE/'result.json').read_text())
assert base_result['success'] and len(base_result['commands'])==13
assert base_result['source_lock_sha256']==lock['frozen_base_lock_sha256']
for rec in base_lock['sources']:assert any(c['sha256']==rec['sha256'] and c['exit_code']==0 for c in base_result['commands'])
for rec in base_lock['sources']:
 rel=pathlib.Path(rec['path']);assert hashlib.sha256((PROJECT/rel).read_bytes()).hexdigest()==rec['sha256']
 src=BASE/'objects'/rel.with_suffix('.olean');meta=json.loads(src.with_suffix('.source-sha256.json').read_text()) if src.with_suffix('.source-sha256.json').exists() else None
 dest=OBJECTS/rel.with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(src)
 old_objects.append({'module_source':rec['path'],'source_sha256':rec['sha256'],'object_path':str(src),'object_sha256':hashlib.sha256(src.read_bytes()).hexdigest()})
CACHE=PROJECT/'.lake/packages';BIN=TOOLING/'lean-4.33.1-darwin_aarch64/bin/lean'
ENV=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[OBJECTS]+[p/'.lake/build/lib/lean' for p in sorted(CACHE.iterdir()) if (p/'.lake/build/lib/lean').is_dir()])))
(SOURCES/'ExactConsumer.lean').write_bytes((HERE/'ExactConsumer.lean').read_bytes());commands=[]
with (HERE/'build.log').open('w') as log:
 for rec in lock['new_sources']+[{'path':'ExactConsumer.lean','sha256':hashlib.sha256((HERE/'ExactConsumer.lean').read_bytes()).hexdigest()}]:
  rel=pathlib.Path(rec['path']);src=SOURCES/rel;assert hashlib.sha256(src.read_bytes()).hexdigest()==rec['sha256'];dst=OBJECTS/rel.with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(BIN),'-o',str(dst),str(src)];p=subprocess.run(cmd,cwd=SOURCES,env=ENV,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log.write(p.stdout);log.flush();commands.append({'path':rec['path'],'sha256':rec['sha256'],'command':cmd,'exit_code':p.returncode,'output':p.stdout});print(rec['path'],p.returncode,flush=True)
  if p.returncode:break
text=(HERE/'build.log').read_text();assert 'sorryAx' not in text
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',text)
assert axioms and all(set(x.strip() for x in a.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'} for a in axioms)
for rec in lock['new_sources']:assert hashlib.sha256((PROJECT/rec['path']).read_bytes()).hexdigest()==rec['sha256']
for rec in old_objects:assert hashlib.sha256(pathlib.Path(rec['object_path']).read_bytes()).hexdigest()==rec['object_sha256']
result={'base_author_receipt_sha256':hashlib.sha256((BASE/'result.json').read_bytes()).hexdigest(),'author':'/root/recover_algebra','scope':'Two fresh bridge sources and literal consumer only; twelve exact source-bound project prerequisite objects reused; no full Target/CI/Comparator claim','success':len(commands)==3 and all(c['exit_code']==0 for c in commands),'fresh_source_commands':len(commands),'reused_project_object_count':len(old_objects),'reused_project_objects':old_objects,'pinned_external_dependency_objects_reused':True,'printed_axiom_lists':axioms,'commands':commands,'source_lock_sha256':hashlib.sha256((HERE/'source-lock.json').read_bytes()).hexdigest()}
(HERE/'result.json').write_text(json.dumps(result,indent=2)+'\n');raise SystemExit(0 if result['success'] else 1)
