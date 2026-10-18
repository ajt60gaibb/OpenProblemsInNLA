#!/usr/bin/env python3
"""Independent exact-copy audit and direct fresh final/wrapper check.

This deliberately reuses shared dependency objects. It is not a fresh entire
closure replay or Linux/Comparator result; the separate immutable full audits
provide those closure checks. Final, statement, frozen statement and wrappers
are re-elaborated from canonical snapshot sources into a new output tree.
"""
import hashlib, json, os, re, shutil, subprocess, tempfile
from pathlib import Path
REPO=Path(__file__).resolve().parents[5]
PKG=REPO/'tensor-computations/TR-14/lean'
SHARED=REPO/'lean-statements'
EVIDENCE=Path(__file__).with_name('inventory-canonical-final-review-1')
LEAN=Path('/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin/lean')
PACKAGES=SHARED/'.lake/packages'
sha=lambda data:hashlib.sha256(data).hexdigest()
def run(argv,**kw):
 p=subprocess.run(list(map(str,argv)),text=True,capture_output=True,**kw)
 return {'argv':list(map(str,argv)),'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
lock_bytes=(PKG/'proof-source-lock.json').read_bytes()
lock=json.loads(lock_bytes)
checks=[]
def check(name,value,**kw):
 checks.append({'name':name,'passed':bool(value),**kw})
copy_records=[]
for r in lock['copies']:
 a=(REPO/r['source']).read_bytes(); b=(REPO/r['destination']).read_bytes()
 ok=sha(a)==r['source_sha256']==sha(b)==r['destination_sha256'] and a==b
 copy_records.append({'module':r['module'],'source':r['source'],'destination':r['destination'],'sha256':sha(a),'passed':ok})
check('all-shared-canonical-copies-exact',all(r['passed'] for r in copy_records),count=len(copy_records))
check('actual-copy-counts',len(copy_records)==78 and sum('/Proofs/' in r['source'] for r in copy_records)==76)
export_records=[]
for name,digest in lock['package_exports'].items():
 data=(PKG/name).read_bytes()
 export_records.append({'path':name,'sha256':sha(data),'expected':digest,'passed':sha(data)==digest})
check('all-explicit-exports-exact',all(r['passed'] for r in export_records),count=len(export_records))
modules={r['module'] for r in copy_records}
check('exact-local-import-closure',all(i in modules for r in lock['copies'] for i in r['imports'] if i.startswith('NLA.')))
check('final-is-root',lock['copies'][-1]['module']=='NLA.Proofs.TR14.Final')
check('literal-frozen-boundary', (PKG/'NLA/Statements/TR14.lean').read_bytes()==(SHARED/'NLA/Statements/TR14.lean').read_bytes() and (PKG/'Reviewed/TR14.lean').read_bytes()==(SHARED/'Reviewed/TR14.lean').read_bytes())
comp=json.loads((PKG/'comparator.json').read_text())
check('comparator-exact-full-target',comp=={'challenge_module':'Challenge','solution_module':'Solution','theorem_names':['NLA.TR14.target'],'definition_names':[],'permitted_axioms':['propext','Classical.choice','Quot.sound']})
manifest=(PKG/'lake-manifest.json').read_bytes()
shared_pins={p['name']:(p['url'],p['rev']) for p in json.loads((SHARED/'lake-manifest.json').read_text())['packages']}
canonical_pins={p['name']:(p['url'],p['rev']) for p in json.loads(manifest)['packages']}
check('manifest-exact-shared-pins',canonical_pins==shared_pins)
deps=[]
for r in json.loads(manifest)['packages']:
 directory=PACKAGES/r['name']
 head=run(['git','-C',directory,'rev-parse','HEAD']); status=run(['git','-C',directory,'status','--porcelain','--untracked-files=no'])
 deps.append({'name':r['name'],'expected':r['rev'],'head':head,'status':status,'passed':head['exit_code']==status['exit_code']==0 and head['stdout'].strip()==r['rev'] and not status['stdout'].strip()})
check('external-dependency-pins-clean',all(d['passed'] for d in deps))
legacy=json.loads((PKG/'boundary-source-lock.json').read_text())
legacy_config=PKG/'reviews/boundary-review-3-evidence/source/lakefile.toml.txt'
check('historical-boundary-config-retained',sha(legacy_config.read_bytes())=='a208407261ad242e449ad06220853c8d5cce5c55faa71132d89f57fcc8f38fd4')
EVIDENCE.mkdir(exist_ok=True)
(EVIDENCE/'audit-driver.py.txt').write_bytes(Path(__file__).read_bytes())
for name in ['proof-source-lock.json','boundary-source-lock.json','lakefile.toml','lake-manifest.json','lean-toolchain','comparator.json']:
 dest=EVIDENCE/'source'/(name+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((PKG/name).read_bytes())
source_names=['NLA/Statements/Infrastructure.lean','NLA/Statements/TR14.lean','NLA/Proofs/TR14/Final.lean','Reviewed/TR14.lean','Identity.lean','Solution.lean']
sources={n:(PKG/n).read_bytes() for n in source_names}
sources['IndependentCanonicalFinal.lean']='''import Solution
import Identity
set_option autoImplicit false
set_option leancert.trust "kernel"
open Lean Elab Command in
elab "#assert_literal_tr14_target " n:ident : command => do
  let decl <- liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (<- getEnv).find? decl with
  | some (.thmInfo info) =>
    unless info.type == mkConst ``NLA.Statements.TR14.Target do
      throwErrorAt n "expected literal unchanged Target with no parameters"
  | _ => throwErrorAt n "expected theorem constant"
#assert_literal_tr14_target NLA.TR14.target
#assert_literal_tr14_target NLA.Proofs.TR14.target
theorem frozen_full_target : NLA.ReviewedStatements.TR14.Target := by
  rw [<- NLA.TR14.target_eq_reviewed]
  exact NLA.TR14.target
#assert_trust kernel NLA.Proofs.TR14.ordinaryWidth_to_symmetricWidth
#assert_trust kernel NLA.Proofs.TR14.target
#assert_trust kernel NLA.TR14.target
#assert_trust kernel NLA.TR14.target_eq_reviewed
#assert_trust kernel frozen_full_target
#print axioms NLA.Proofs.TR14.ordinaryWidth_to_symmetricWidth
#print axioms NLA.Proofs.TR14.target
#print axioms NLA.TR14.target
#print axioms NLA.TR14.target_eq_reviewed
#print axioms frozen_full_target
'''.encode()
for name,data in sources.items():
 target=EVIDENCE/'source'/(name+'.txt');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
reused=[]
for r in lock['copies']:
 if r['module'].replace('.','/')+'.lean' in sources: continue
 obj=SHARED/'.lake/build/lib/lean'/(r['module'].replace('.','/')+'.olean')
 reused.append({'module':r['module'],'source_sha256':r['source_sha256'],'object':str(obj),'object_sha256':sha(obj.read_bytes())})
result={'reviewer':'/root/solved_inventory (AI agent)','scope':'Independent exact-copy/source-fidelity audit and direct fresh canonical Final/Identity/Solution re-elaboration with reused shared support objects; NOT full fresh closure replay, NOT Linux or Comparator','source_approval_scope':['Final','Identity','Solution','canonical statement and frozen boundary fidelity','exact copied import closure and package exports'],'self_authored_TR14_modules_excluded_from_independent_source_approval':['ProductStabilizer','ContextualReduced','UnitSpan','UnitScaleProducts','LinearTransformation','UnitScaleAction','UnitTransformation','UnitAvoidance','ContextualProductStep','ContextualProduct','MinimumOrdinary','OrdinaryGraph','OrdinaryGraphUnits','UnitProductScaling','GraphNormalization','GraphQuotientContext','GraphListContext','ScalarGraphSeparation','GraphBlockModeDimension','NormalizedOrdinaryLower'],'proof_source_lock_sha256':sha(lock_bytes),'source_sha256':{n:sha(d) for n,d in sources.items()},'copy_records':copy_records,'export_records':export_records,'checks':checks,'dependencies':deps,'lean_version':run([LEAN,'--version']),'lean_sha256':sha(LEAN.read_bytes()),'reused_shared_dependency_objects':reused,'commands':[]}
if not all(c['passed'] for c in checks):
 (EVIDENCE/'result.json').write_text(json.dumps(result,indent=2)+'\n'); raise SystemExit('static fidelity check failed')
with tempfile.TemporaryDirectory(prefix='tr14-independent-canonical-direct-') as tmp:
 temp=Path(tmp);src=temp/'source';obj=temp/'objects';src.mkdir();obj.mkdir()
 for dep in reused:
  original=Path(dep['object']);target=obj/(dep['module'].replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(original,target)
 paths=[obj,SHARED/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in PACKAGES.iterdir() if (p/'.lake/build/lib/lean').is_dir()]
 env=dict(os.environ,PATH=str(LEAN.parent)+':'+os.environ['PATH'],LEAN_PATH=':'.join(map(str,paths)))
 result['LEAN_PATH']=env['LEAN_PATH']
 for index,(name,data) in enumerate(sources.items()):
  path=src/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
  out=obj/Path(name).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  r=run([LEAN,'-o',out,name],cwd=src,env=env)
  log=EVIDENCE/(f'{index+1:02d}-'+name.replace('/','_')+'.log')
  log.write_text(r['stdout']+r['stderr'])
  r['source']=name;r['source_sha256']=sha(data);r['log']=log.name;r['log_sha256']=sha(log.read_bytes())
  if out.is_file():r['object_sha256']=sha(out.read_bytes())
  result['commands'].append(r)
  print(f'{name}: {r["exit_code"]}',flush=True)
  if r['exit_code']!=0:break
allowed={'propext','Classical.choice','Quot.sound'}
axioms=[]
for r in result['commands']:
 for raw in re.findall(r'depends on axioms:\s*\[([^]]*)\]',r['stdout']):
  axioms.extend(x.strip() for x in raw.split(',') if x.strip())
result['observed_axioms']=sorted(set(axioms))
result['source_unchanged_after']={n:(PKG/n).read_bytes()==sources[n] for n in source_names}
result['lock_unchanged_after']=(PKG/'proof-source-lock.json').read_bytes()==lock_bytes
result['passed']=all(c['passed'] for c in checks) and len(result['commands'])==len(sources) and all(r['exit_code']==0 for r in result['commands']) and set(axioms)<=allowed and all(result['source_unchanged_after'].values()) and result['lock_unchanged_after']
(EVIDENCE/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':result['passed'],'commands':len(result['commands']),'copies':len(copy_records),'exports':len(export_records)}),flush=True)
raise SystemExit(0 if result['passed'] else 1)
