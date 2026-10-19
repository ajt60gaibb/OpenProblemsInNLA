from pathlib import Path
import json,hashlib,re,subprocess,os,time
repo=Path('/private/tmp/nla-pf05-lean-oct18'); package=repo/'nonnegative-and-positive-factorizations/PF-05/lean'
audit=Path('/private/tmp/nla-pf05-next-preproof/independent-review-2/package-boundary-audit');audit.mkdir(exist_ok=True)
source=audit/'source';objects=audit/'objects';logs=audit/'logs'
for p in [source,objects,logs]:p.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
lock=json.loads((package/'pre-solution-boundary-lock.json').read_text())
checks=[]
assert sha(package/'pre-solution-boundary-lock.json')=='c0196c6806961a084f6474809e7ac0d60019ae8433455bb2775465329a0a694e'
for row in lock['copies']:
 a=repo/row['source'];b=repo/row['destination'];ok=sha(a)==sha(b)==row['source_sha256']==row['destination_sha256'];checks.append(dict(kind='source-copy',module=row['module'],passed=ok))
for rel,digest in lock['exports'].items():checks.append(dict(kind='boundary-file',path=rel,passed=sha(package/rel)==digest))
checks.append(dict(kind='Solution-absent',passed=not(package/'Solution.lean').exists()))
checks.append(dict(kind='Challenge-exact',passed=(package/'Challenge.lean').read_text()=='''import NLA.Statements.PF05

/-! Exact frozen PF-05 Target; comparison placeholder only. -/
set_option autoImplicit false

namespace NLA.PF05

theorem target : NLA.Statements.PF05.Target := by
  sorry

end NLA.PF05
'''))
comp=json.loads((package/'comparator.json').read_text());checks.append(dict(kind='comparator',passed=comp.get('theorem_names')==['NLA.PF05.target'] and comp.get('definition_names')==[] and set(comp.get('permitted_axioms',[]))=={'propext','Classical.choice','Quot.sound'}))
shared_manifest=json.loads((repo/'lean-statements/lake-manifest.json').read_text());manifest=json.loads((package/'lake-manifest.json').read_text())
checks.append(dict(kind='dependency-revisions',passed={r['name']:r['rev'] for r in manifest['packages']}=={r['name']:r['rev'] for r in shared_manifest['packages']}))
checks.append(dict(kind='reviewed-exact',passed=(package/'Reviewed/PF05.lean').read_bytes()==(repo/'lean-statements/Reviewed/PF05.lean').read_bytes()))
checks.append(dict(kind='toolchain',passed=(package/'lean-toolchain').read_bytes()==(repo/'lean-statements/lean-toolchain').read_bytes()))
(audit/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
assert all(c['passed'] for c in checks),[c for c in checks if not c['passed']]
files=['NLA/Statements/Infrastructure.lean','NLA/Statements/PF05.lean','Reviewed/PF05.lean','Challenge.lean','Identity.lean']
input_hashes={}
for rel in files:
 data=(package/rel).read_bytes();dest=source/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data);input_hashes[rel]=sha(package/rel)
(audit/'input-lock.json').write_text(json.dumps(input_hashes,indent=2)+'\n')
bin=Path('/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin');cache=repo/'lean-statements/.lake/packages'
paths=[objects]+[p/'.lake/build/lib/lean' for p in cache.iterdir() if(p/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,PATH=str(bin)+':'+os.environ['PATH'],LEAN_PATH=':'.join(map(str,paths)))
results=[]
for rel in files:
 out=objects/Path(rel).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 proc=subprocess.run([str(bin/'lean'),'-o',str(out),rel],cwd=source,env=env,text=True,capture_output=True)
 (logs/(rel.replace('/','-')+'.log')).write_text(proc.stdout+proc.stderr);results.append(dict(source=rel,exit_code=proc.returncode));assert proc.returncode==0,rel
(source/'BoundaryConsumer.lean').write_text('''import Identity
set_option leancert.trust "kernel"
example : NLA.Statements.PF05.Target = NLA.ReviewedStatements.PF05.Target := rfl
#assert_trust kernel NLA.PF05.target_eq_reviewed
#print axioms NLA.PF05.target_eq_reviewed
''')
proc=subprocess.run([str(bin/'lean'),'BoundaryConsumer.lean'],cwd=source,env=env,text=True,capture_output=True);(logs/'boundary-consumer.log').write_text(proc.stdout+proc.stderr);assert proc.returncode==0
(source/'ChallengeKernelRejection.lean').write_text('''import Challenge
set_option leancert.trust "kernel"
#assert_trust kernel NLA.PF05.target
''')
negative=subprocess.run([str(bin/'lean'),'ChallengeKernelRejection.lean'],cwd=source,env=env,text=True,capture_output=True);(logs/'challenge-expected-kernel-rejection.log').write_text(negative.stdout+negative.stderr)
expected=negative.returncode!=0 and 'sorryAx' in negative.stdout+negative.stderr
unchanged=all(sha(package/r)==d for r,d in input_hashes.items())
result=dict(status='PASS' if expected and unchanged else 'FAIL',checks=len(checks),copied_sources=len(lock['copies']),fresh_builds=results,identity_consumer_exit_code=proc.returncode,expected_placeholder_kernel_rejection=expected,boundary_sources_unchanged=unchanged,solution_absent=not(package/'Solution.lean').exists(),lock_sha256=sha(package/'pre-solution-boundary-lock.json'))
(audit/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));raise SystemExit(0 if result['status']=='PASS' else 1)
