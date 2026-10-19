import pathlib, hashlib, re, json, os, subprocess, time
base=pathlib.Path('/private/tmp/nla-pf05-lean-oct18/lean-statements')
audit=pathlib.Path(__file__).resolve().parent
src=audit/'source'; obj=audit/'objects'; logs=audit/'logs'
for p in (src,obj,logs): p.mkdir(exist_ok=True)
heads=['NLA.Proofs.PF05.CommonChart','NLA.Proofs.PF05.ConicCongruence']
modules=[]; seen=set(); locks={}
def visit(name):
    if not name.startswith('NLA.') or name in seen:return
    seen.add(name)
    rel=pathlib.Path(name.replace('.','/')+'.lean'); data=(base/rel).read_bytes()
    text=data.decode()
    for dep in re.findall(r'^import\s+(\S+)',text,re.M): visit(dep)
    (src/rel).parent.mkdir(parents=True,exist_ok=True); (src/rel).write_bytes(data)
    locks[str(rel)]=hashlib.sha256(data).hexdigest(); modules.append(name)
for head in heads:visit(head)
(audit/'input-lock.json').write_text(json.dumps(locks,indent=2)+'\n')
bin=pathlib.Path('/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin')
packages=[p/'.lake/build/lib/lean' for p in (base/'.lake/packages').iterdir() if (p/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,PATH=str(bin)+':'+os.environ['PATH'],LEAN_PATH=':'.join(map(str,[obj]+packages)))
results=[]
for i,name in enumerate(modules):
    rel=pathlib.Path(name.replace('.','/')+'.lean'); output=obj/rel.with_suffix('.olean'); output.parent.mkdir(parents=True,exist_ok=True)
    t=time.time(); proc=subprocess.run([str(bin/'lean'),'-o',str(output),str(rel)],cwd=src,env=env,capture_output=True,text=True)
    (logs/f'{i:02}-{name}.log').write_text(proc.stdout+proc.stderr)
    results.append(dict(module=name,exit_code=proc.returncode,seconds=time.time()-t))
    if proc.returncode:
        (audit/'result.json').write_text(json.dumps(dict(status='FAIL',builds=results),indent=2)+'\n');raise SystemExit(proc.returncode)
consumer='import NLA.Proofs.PF05.CommonChart\nimport NLA.Proofs.PF05.ConicCongruence\nset_option leancert.trust "kernel"\n'
constants=[
'NLA.Proofs.PF05.CommonChart.lowerShear_det','NLA.Proofs.PF05.CommonChart.lowerShear_inv',
'NLA.Proofs.PF05.CommonChart.exists_common_nonroot','NLA.Proofs.PF05.CommonChart.exists_common_chart',
'NLA.Proofs.PF05.ConicDeterminant.conic_coefficients','NLA.Proofs.PF05.ConicDeterminant.determinant_scale',
'NLA.Proofs.PF05.ConicDeterminant.metric_identity','NLA.Proofs.PF05.ConicDeterminant.scale_cube','NLA.Proofs.PF05.ConicDeterminant.scale_pos',
'NLA.Proofs.PF05.ConicPositive.primal_outer_psd','NLA.Proofs.PF05.ConicPositive.primal_inv_outer_psd','NLA.Proofs.PF05.ConicPositive.dual_inv_outer_psd',
'NLA.Proofs.PF05.ConicCongruence.actual_rank','NLA.Proofs.PF05.ConicCongruence.operator_congruence','NLA.Proofs.PF05.ConicCongruence.congruent_of_conic_alternative']
for c in constants: consumer+=f'#check {c}\n#assert_trust kernel {c}\n#print axioms {c}\n'
(src/'Consumer.lean').write_text(consumer)
proc=subprocess.run([str(bin/'lean'),str(src/'Consumer.lean')],cwd=src,env=env,capture_output=True,text=True)
(logs/'consumer.log').write_text(proc.stdout+proc.stderr)
unchanged=all(hashlib.sha256((base/pathlib.Path(rel)).read_bytes()).hexdigest()==sha for rel,sha in locks.items())
result=dict(status='PASS' if proc.returncode==0 and unchanged else 'FAIL',source_count=len(modules),consumer_constants=len(constants),source_unchanged=unchanged,consumer_exit_code=proc.returncode,builds=results)
(audit/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='builds'}))
raise SystemExit(0 if result['status']=='PASS' else 1)
