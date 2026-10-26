#!/usr/bin/env python3
"""Exact post-boundary PF05 delta and direct canonical wrapper kernel checks.
Reuses recorded shared proof objects, explicitly NOT a fresh whole closure audit.
"""
import argparse,hashlib,json,os,re,shutil,subprocess,tempfile,tomllib
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path.cwd());args=ap.parse_args();root=args.root.resolve()
package=root/'nonnegative-and-positive-factorizations/PF-05/lean';shared=root/'lean-statements';evidence=root/'docs/lean/proofs/PF-05/campaign-2026-10-18/post-boundary-delta-review-1-evidence';evidence.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest();checks={}
def check(k,v):checks[k]=bool(v)
oldbytes=(package/'pre-solution-boundary-lock.json').read_bytes();old=json.loads(oldbytes);newbytes=(package/'proof-source-lock.json').read_bytes();new=json.loads(newbytes)
check('historical_lock_unchanged',sha(oldbytes)=='c0196c6806961a084f6474809e7ac0d60019ae8433455bb2775465329a0a694e')
check('42_exact_original_copies',len(old['copies'])==len(new['copies'])==42 and old['copies']==new['copies'])
for item in old['copies']:
 a=(root/item['source']).read_bytes();b=(root/item['destination']).read_bytes();check('copied:'+item['module'],a==b and sha(a)==item['source_sha256']==item['destination_sha256'])
for name,h in old['exports'].items():
 if name!='lakefile.toml':check('old_export_unchanged:'+name,sha((package/name).read_bytes())==h)
for name,h in new['package_exports'].items():check('new_export_locked:'+name,sha((package/name).read_bytes())==h)
snapshot=package/'reviews/pre-solution-boundary-review-1-snapshot';before=tomllib.loads((snapshot/'lakefile.toml.txt').read_text());after=tomllib.loads((package/'lakefile.toml').read_text())
expected=json.loads(json.dumps(before));expected['defaultTargets'].append('Solution');expected['lean_lib'].append({'name':'Solution'});check('only_intentional_Lake_delta',after==expected)
solution=(package/'Solution.lean').read_text();imports=re.findall(r'^import (.+)$',solution,re.M);check('Solution_imports_Final_Identity_only',imports==['NLA.Proofs.PF05.Final','Identity']);check('Solution_exact_full_Target_wrapper','theorem target : NLA.Statements.PF05.Target := by\n  exact NLA.Proofs.PF05.target' in solution and '#assert_trust kernel target' in solution and not re.search(r'\b(sorry|axiom)\b',solution))
check('selected_export_exact','export' in new and new['export']=='NLA.PF05.target');check('shared_Final_frozen',sha((shared/'NLA/Proofs/PF05/Final.lean').read_bytes())=='9fec01759722b38b8fab73a3115f9b6546df3cba1bdb7b51f53e0b8c3b3db0d9')
check('two_boundary_approvals_retained',(package/'reviews/PRE_SOLUTION_BOUNDARY_REVIEW_1_2026-10-18.md').exists() and (package/'reviews/PACKAGE_BOUNDARY_REVIEW_1_2026-10-18.md').exists())
check('Challenge_absent_from_proof_imports',all('Challenge' not in x['imports'] for x in new['copies']))
consumer='''import Solution
import LeanCert.Tactic.Verification
open Lean Elab Command in
elab "#assert_exact_selected_pf05_export" : command => do
  let name := ``NLA.PF05.target
  match (← getEnv).find? name with
  | some (.thmInfo info) =>
    unless info.type == mkConst ``NLA.Statements.PF05.Target do
      throwError "expected the exact literal unchanged Target, without parameters"
  | _ => throwError "expected proved theorem declaration"
#assert_exact_selected_pf05_export
#assert_trust kernel NLA.PF05.target
#assert_trust kernel NLA.PF05.target_eq_reviewed
#print axioms NLA.PF05.target
#print axioms NLA.PF05.target_eq_reviewed
'''
inputs={n:(package/n).read_bytes() for n in ['NLA/Statements/Infrastructure.lean','NLA/Statements/PF05.lean','Reviewed/PF05.lean','Identity.lean','Solution.lean']};inputs['ExactCanonicalPF05Export.lean']=consumer.encode()
for n,data in inputs.items():p=evidence/'source'/(n+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
for n in ['proof-source-lock.json','pre-solution-boundary-lock.json','lakefile.toml','comparator.json','lake-manifest.json','lean-toolchain']:(evidence/(n+'.txt')).write_bytes((package/n).read_bytes())
(evidence/'audit-driver.py.txt').write_bytes(Path(__file__).read_bytes())
lean=Path('/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin/lean');cache=shared/'.lake/packages';objects=shared/'.lake/build/lib/lean'
reused=[]
for item in new['copies']:
 if '.Proofs.' in item['module']:
  path=objects/(item['module'].replace('.','/')+'.olean');data=path.read_bytes();reused.append({'module':item['module'],'path':str(path),'olean_sha256':sha(data),'source_sha256':item['source_sha256'],'independently_source_rebuilt_in_prior_whole_audit':True})
result={'scope':'Post-boundary exact-copy/delta review and direct canonical statements/Identity/Solution/export consumer. Forty shared proof objects explicitly reused, NOT a fresh whole canonical proof closure. Separate verifier supplies fresh 47-command canonical audit.','reviewer':'/root/solved_inventory','checks':checks,'proof_source_lock_sha256':sha(newbytes),'pre_solution_boundary_lock_sha256':sha(oldbytes),'source_sha256':{n:sha(d) for n,d in inputs.items()},'reused_shared_proof_objects':reused,'commands':[],'authoritative_linux_comparator':False}
with tempfile.TemporaryDirectory(prefix='pf05-canonical-export-review-1-') as temp:
 temp=Path(temp);src=temp/'source';out=temp/'output';out.mkdir();libs=[p/'.lake/build/lib/lean' for p in sorted(cache.iterdir()) if (p/'.lake/build/lib/lean').is_dir()];env=dict(os.environ,LEAN_PATH=':'.join(map(str,[out,objects,*libs,lean.parent.parent/'lib/lean'])))
 result['lean_path']=env['LEAN_PATH']
 for item in reused:
  destination=out/(item['module'].replace('.','/')+'.olean');destination.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(item['path'],destination);destination.chmod(0o444)
 result['reused_objects_copied_into_output_for_module_resolution']=True
 for n,data in inputs.items():
  p=src/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);p.chmod(0o444)
 for n in inputs:
  output=out/Path(n).with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True);argv=[str(lean),'-R',str(src),'-o',str(output),str(src/n)];p=subprocess.run(argv,cwd=src,env=env,text=True,capture_output=True,timeout=180);r={'source':n,'argv':argv,'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr};result['commands'].append(r);(evidence/(n.replace('/','-')+'.log')).write_text(p.stdout+p.stderr);print(n,p.returncode,flush=True)
  if p.returncode:break
result['source_unchanged_after']={n:(package/n).read_bytes()==d for n,d in inputs.items() if n!='ExactCanonicalPF05Export.lean'}
result['objects_unchanged_after']={x['module']:sha(Path(x['path']).read_bytes())==x['olean_sha256'] for x in reused}
axioms={a.strip() for r in result['commands'] for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]',r['stdout'],re.S) for a in group.split(',') if a.strip()};result['printed_axioms']=sorted(axioms)
result['passed']=all(checks.values()) and len(result['commands'])==len(inputs) and all(r['exit_code']==0 for r in result['commands']) and all(result['source_unchanged_after'].values()) and all(result['objects_unchanged_after'].values()) and axioms<={'propext','Classical.choice','Quot.sound'}
(evidence/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'passed':result['passed'],'checks':len(checks),'commands':len(result['commands']),'reused_proof_objects':len(reused),'failed_checks':[k for k,v in checks.items() if not v]},indent=2));raise SystemExit(0 if result['passed'] else 1)
