from pathlib import Path
import subprocess,hashlib,json,datetime,re,tempfile,os
root=Path(__file__).resolve().parents[2];evidence=Path(__file__).resolve().parent
build=Path(tempfile.mkdtemp(prefix='nla-ie21-complete-author-',dir='/private/tmp'))
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean=Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(build),str(root)]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
config=json.loads((root/'comparator.json').read_text());names=config['theorem_names'];assert len(names)==23
freeze=json.loads((root/'reviews/statement-freeze.json').read_text())
for f,h in freeze['mathematical_boundary_sha256'].items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h
sources={str(f.relative_to(root)).removesuffix('.lean').replace('/','.'):f for f in (root/'NLA/IE21').glob('*.lean')}
order=[];active=set()
def visit(name):
 if name in order:return
 assert name not in active, name
 active.add(name)
 for imp in re.findall(r'^import\s+(NLA\.IE21\.\w+)\s*$',sources[name].read_text(),re.M):
  assert imp in sources,imp
  visit(imp)
 active.remove(name);order.append(name)
visit('NLA.IE21.FiniteSize')
assert set(order)==set(sources),(set(sources)-set(order))
hashes={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sources.values()}
audit=evidence/'Axioms.lean';audit.write_text('import NLA.IE21.FiniteSize\n'+''.join('#print axioms '+n+'\n' for n in names))
commands=[];logpath=evidence/'typecheck.log'
with logpath.open('w') as log:
 log.write('Complete local development proof-source rebuild; cached pinned dependency artifacts. No actual LeanCert/Comparator/Linux claim.\n')
 log.write(subprocess.check_output([str(lean),'--version'],text=True))
 for name in order+['Axioms']:
  f=sources[name] if name!='Axioms' else audit
  cmd=[str(lean)]
  if name!='Axioms':
   out=build/Path(name.replace('.','/')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);cmd+=['-o',str(out)]
  cmd+=[str(f.relative_to(root))]
  log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
  r=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log.write(r.stdout+'EXIT '+str(r.returncode)+'\n');log.flush();print(name,r.returncode,flush=True)
  commands.append({'source':str(f.relative_to(root)),'exit_code':r.returncode,'output':r.stdout})
  if r.returncode:raise SystemExit(r.returncode)
  assert not re.search(r'\b(?:warning|error):',r.stdout),r.stdout
assert hashes=={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sources.values()}
axiom_output=commands[-1]['output'];found={}
for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",axiom_output):found[name]=[x.strip() for x in axioms.split(',') if x.strip()]
assert set(found)==set(names),found
assert all(set(x)<=set(config['permitted_axioms']) for x in found.values())
record={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'author':'Codex AI root; proof author, not independent whole-problem referee','all_selected_targets_compiled':True,'target_count':len(names),'project_sources_built':len(order),'build_directory':str(build),'source_hashes':hashes,'command_results':commands,'selected_axiom_closures':found,'frozen_boundary_sha256':freeze['mathematical_boundary_sha256'],'evidence_sha256':{'build.py':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'Axioms.lean':hashlib.sha256(audit.read_bytes()).hexdigest(),'typecheck.log':hashlib.sha256(logpath.read_bytes()).hexdigest()},'limits':['Local cached dependency build; no fresh dependency-source authentication','No authentic LeanCert assertion execution or actual Linux Comparator execution in this local run','Fresh independent final reviews and full reproducible gates remain required']}
(evidence/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS all23 selected exact proof declarations, permitted axiom closures, unchanged inputs',flush=True)
