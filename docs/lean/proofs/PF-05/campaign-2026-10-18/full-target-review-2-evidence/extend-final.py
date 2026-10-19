import pathlib, hashlib, re, json, os, subprocess, time
base=pathlib.Path('/private/tmp/nla-pf05-lean-oct18/lean-statements')
audit=pathlib.Path(__file__).resolve().parent
src=audit/'source';obj=audit/'objects';logs=audit/'logs'
previous=json.loads((audit/'result.json').read_text())
assert previous['status']=='PASS'
locks=json.loads((audit/'input-lock.json').read_text()); prelocks=dict(locks)
seen=set();new=[];closure=[]
def visit(name):
    if not name.startswith(('NLA.','Reviewed.')) or name in seen:return
    seen.add(name);rel=pathlib.Path(name.replace('.','/')+'.lean');data=(base/rel).read_bytes();sha=hashlib.sha256(data).hexdigest()
    if str(rel) in prelocks:assert prelocks[str(rel)]==sha
    for dep in re.findall(r'^import\s+(\S+)',data.decode(),re.M):visit(dep)
    closure.append(name)
    if str(rel) in prelocks:return
    (src/rel).parent.mkdir(parents=True,exist_ok=True);(src/rel).write_bytes(data);locks[str(rel)]=sha;new.append(name)
visit('NLA.Proofs.PF05.Final');visit('Reviewed.PF05')
(audit/'full-input-lock.json').write_text(json.dumps(locks,indent=2)+'\n')
bin=pathlib.Path('/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin')
packages=[p/'.lake/build/lib/lean' for p in (base/'.lake/packages').iterdir() if (p/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,PATH=str(bin)+':'+os.environ['PATH'],LEAN_PATH=':'.join(map(str,[obj]+packages)))
results=[]
for i,name in enumerate(new):
    rel=pathlib.Path(name.replace('.','/')+'.lean'); output=obj/rel.with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
    t=time.time();proc=subprocess.run([str(bin/'lean'),'-o',str(output),str(rel)],cwd=src,env=env,capture_output=True,text=True)
    (logs/f'final-{i:02}-{name}.log').write_text(proc.stdout+proc.stderr)
    results.append(dict(module=name,exit_code=proc.returncode,seconds=time.time()-t))
    if proc.returncode:
        (audit/'full-result.json').write_text(json.dumps(dict(status='FAIL',new_builds=results),indent=2)+'\n');raise SystemExit(proc.returncode)
consumer='''import NLA.Proofs.PF05.Final
import Reviewed.PF05
set_option leancert.trust "kernel"
example : NLA.Statements.PF05.Target := NLA.Proofs.PF05.target
example : NLA.ReviewedStatements.PF05.Target := NLA.Proofs.PF05.target
example : NLA.Statements.PF05.Target = NLA.ReviewedStatements.PF05.Target := rfl
'''
constants=['NLA.Proofs.PF05.target','NLA.Proofs.PF05.rigid_implies_unique','NLA.Proofs.PF05.positive_rigid_implies_unique','NLA.Proofs.PF05.unique_implies_infinitesimallyRigid','NLA.Proofs.PF05.ZeroRestriction.exists_positive_core_of_no_nonzero_zero_pair','NLA.Proofs.PF05.ZeroRestriction.rigid_iff_reduced','NLA.Proofs.PF05.ZeroRestriction.unique_iff_reduced']
for c in constants:consumer+=f'#check {c}\n#assert_trust kernel {c}\n#print axioms {c}\n'
(src/'FinalConsumer.lean').write_text(consumer)
proc=subprocess.run([str(bin/'lean'),str(src/'FinalConsumer.lean')],cwd=src,env=env,capture_output=True,text=True)
(logs/'final-consumer.log').write_text(proc.stdout+proc.stderr)
unchanged=all(hashlib.sha256((base/pathlib.Path(rel)).read_bytes()).hexdigest()==sha for rel,sha in locks.items())
result=dict(status='PASS' if proc.returncode==0 and unchanged else 'FAIL',total_source_count=len(locks),literal_target_closure_count=len(closure),new_source_count=len(new),consumer_constants=len(constants),source_unchanged=unchanged,consumer_exit_code=proc.returncode,earlier_result_sha256=hashlib.sha256((audit/'result.json').read_bytes()).hexdigest(),new_builds=results)
(audit/'full-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='new_builds'}));raise SystemExit(0 if result['status']=='PASS' else 1)
