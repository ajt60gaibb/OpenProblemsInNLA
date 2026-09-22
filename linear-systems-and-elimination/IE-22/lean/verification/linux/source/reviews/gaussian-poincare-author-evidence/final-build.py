from pathlib import Path
import os,subprocess,sys,hashlib,json,tempfile,datetime,re
root=Path(__file__).resolve().parents[2]; evidence=Path(__file__).resolve().parent
build=Path(tempfile.mkdtemp(prefix='nla-ie22-gaussian-variance-final-',dir='/private/tmp'))
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
previous=root.parents[1]/'IE-21/lean'
cache_receipt=previous/'reviews/ie21-final-fidelity-evidence/build-receipt.json'
cache=json.loads(cache_receipt.read_text())
dep_receipt=root/'reviews/IE21-DEPENDENCY.json'
deps=json.loads(dep_receipt.read_text())['source_sha256']
for f,h in deps.items():assert digest(root/f)==h
assert len(deps)==31
(build/'NLA').mkdir()
(build/'NLA/IE21').symlink_to(Path(cache['build_directory'])/'NLA/IE21',target_is_directory=True)
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean=Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
sources=['NLA/IE22/Definitions.lean','NLA/IE22/VarianceTensorization.lean','NLA/IE22/GaussianPoincare.lean','NLA/IE22/GaussianPoincareHinge.lean','NLA/IE22/GaussianVariance.lean','reviews/gaussian-poincare-author-evidence/FinalAxioms.lean']
before={f:digest(root/f) for f in sources}
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(build),str(root)]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
records=[];logpath=evidence/'final-typecheck.log'
with logpath.open('w') as log:
 log.write('Fresh IE22 Gaussian variance author rebuild; cached unchanged verified IE21 modules and pinned third-party dependencies; not full Linux verification.\n')
 for f in sources:
  out=build/Path(f).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(lean),'-o',str(out),f];log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
  p=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log.write(p.stdout+'EXIT '+str(p.returncode)+'\n');log.flush()
  records.append({'source':f,'command':cmd,'exit_code':p.returncode,'output_sha256':hashlib.sha256(p.stdout.encode()).hexdigest()})
  print(f,p.returncode,flush=True)
  if p.returncode:raise SystemExit(p.returncode)
assert all(digest(root/f)==h for f,h in before.items())
logtext=logpath.read_text();assert 'warning:' not in logtext and 'error:' not in logtext
closures=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",logtext)
expected=[n for f in sources[2:5] for n in re.findall(r'^theorem ([A-Za-z0-9_]+)',(root/f).read_text(),re.M)]
assert len(closures)==len(expected)
assert {n for n,_ in closures}=={'NLA.IE22.'+n for n in expected}
allowed={'propext','Classical.choice','Quot.sound'}
for n,ax in closures:assert set(ax.split(', '))<=allowed
receipt={'schema':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'AI proof author /root/infrastructure_audit, not an independent final reviewer','selected_target':'NLA.IE22.gaussian_objective_variance','scope':'Exact frozen selected signature, fresh author rebuild and all owned public theorem axiom closures; no full Linux/Comparator claim','build_directory':str(build),'lean_binary':str(lean),'lean_binary_sha256':digest(lean),'source_sha256':before,'source_unchanged_after':True,'commands':records,'log_sha256':digest(logpath),'script_sha256':digest(Path(__file__)),'closures':{n:ax.split(', ') for n,ax in closures},'vendored_ie21_receipt_sha256':digest(dep_receipt),'vendored_ie21_sources':deps,'reused_ie21_build_receipt':str(cache_receipt),'reused_ie21_build_receipt_sha256':digest(cache_receipt),'reused_ie21_olean_sha256':{f:str(digest(Path(cache['build_directory'])/Path(f).with_suffix('.olean'))) for f in deps},'limitations':['Cached third-party package oleans and unchanged verified IE21 oleans reused; no independently authenticated local package Git trees.','Whole-package Linux kernel replay, authentic LeanCert and Comparator still required before IE22 completion.']}
(evidence/'final-author-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'build_directory':str(build),'closures':len(closures),'selected_source_sha256':before['NLA/IE22/GaussianVariance.lean'],'result':'PASS'}),flush=True)
