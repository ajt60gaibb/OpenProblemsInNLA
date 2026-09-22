from pathlib import Path
import os,subprocess,hashlib,json,tempfile,datetime,re
root=Path(__file__).resolve().parents[2];evidence=Path(__file__).resolve().parent
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
author_receipt=root/'reviews/root-proof-evidence/spherical-author-receipt.json'
expected=json.loads(author_receipt.read_text())['source_sha256']
for f,h in expected.items():assert digest(root/f)==h
freeze=root/'reviews/statement-freeze.json'
boundary=json.loads(freeze.read_text())['mathematical_boundary_sha256']
for f,h in boundary.items():assert digest(root/f)==h
previous=root.parents[1]/'IE-21/lean'
cache_receipt=previous/'reviews/ie21-final-fidelity-evidence/build-receipt.json'
cache=json.loads(cache_receipt.read_text())
dep_receipt=root/'reviews/IE21-DEPENDENCY.json';deps=json.loads(dep_receipt.read_text())['source_sha256']
for f,h in deps.items():assert digest(root/f)==h
assert len(deps)==31
build=Path(tempfile.mkdtemp(prefix='nla-ie22-supremum-spherical-referee-',dir='/private/tmp'))
(build/'NLA').mkdir();(build/'NLA/IE21').symlink_to(Path(cache['build_directory'])/'NLA/IE21',target_is_directory=True)
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean=Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
sources=['NLA/IE22/Definitions.lean','NLA/IE22/SupremumSemantics.lean','NLA/IE22/SphericalRealization.lean','reviews/supremum-spherical-referee-infrastructure-evidence/ExactTypesAndAxioms.lean']
before={f:digest(root/f) for f in sources};records=[]
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(build),str(root)]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
logpath=evidence/'typecheck.log'
with logpath.open('w') as log:
 log.write('Independent partial module review by AI /root/infrastructure_audit, no authorship in the reviewed modules, authored other IE22 and vendored IE21 modules; cached dependencies, no full Linux claim.\n')
 for f in sources:
  out=build/Path(f).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(lean),'-o',str(out),f];log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
  p=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log.write(p.stdout+'EXIT '+str(p.returncode)+'\n');log.flush()
  records.append({'source':f,'command':cmd,'exit_code':p.returncode,'output_sha256':hashlib.sha256(p.stdout.encode()).hexdigest()})
  print(f,p.returncode,flush=True)
  if p.returncode:raise SystemExit(p.returncode)
assert all(digest(root/f)==h for f,h in before.items())
text=logpath.read_text();assert 'warning:' not in text and 'error:' not in text
closures=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)
names=[n for f in sources[1:3] for n in re.findall(r'^(?:theorem|lemma) ([A-Za-z0-9_]+)',(root/f).read_text(),re.M)]
assert {n for n,_ in closures}=={'NLA.IE22.'+n for n in names}
for n,a in closures:assert {v for v in a.split(', ') if v}<={'propext','Classical.choice','Quot.sound'}
receipt={'schema':1,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'AI /root/infrastructure_audit','independence':'No authorship or source edits in SupremumSemantics or SphericalRealization. Authored separate IE22 Gaussian modules and some reused IE21 modules; module-only independent review, not final whole-package review.','build_directory':str(build),'lean_binary_sha256':digest(lean),'source_sha256':before,'source_unchanged_after':True,'mathematical_boundary_sha256':boundary,'statement_freeze_sha256':digest(freeze),'author_receipt_sha256':digest(author_receipt),'exact_selected_names':['supremum_semantics','constant_semantics','spherical_realization_from_finite_bound','high_aspect_near_extremizers'],'commands':records,'log_sha256':digest(logpath),'script_sha256':digest(Path(__file__)),'closures':{n:a.split(', ') if a else [] for n,a in closures},'IE21_dependency_receipt_sha256':digest(dep_receipt),'reused_ie21_build_receipt_sha256':digest(cache_receipt),'reused_ie21_olean_sha256':{f:digest(Path(cache['build_directory'])/Path(f).with_suffix('.olean')) for f in deps},'limitations':['Pinned dependency oleans and unchanged verified IE21 cache reused; source-only pinned Mathlib extraction has no Git metadata, not independently authenticated local third-party binaries.','No full Linux kernel replay, LeanCert or Comparator claim.']}
(evidence/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'result':'PASS','public_closures':len(closures),'build_directory':str(build)}),flush=True)
