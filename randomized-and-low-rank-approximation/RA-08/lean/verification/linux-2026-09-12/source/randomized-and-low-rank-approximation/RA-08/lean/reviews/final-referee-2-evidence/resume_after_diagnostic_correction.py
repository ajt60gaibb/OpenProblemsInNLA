from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
P=Path('/tmp/nla-lean-ra08-worktree/randomized-and-low-rank-approximation/RA-08/lean')
E=P/'reviews/final-referee-2-evidence'
R=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda n,x:(E/n).write_text(json.dumps(x,indent=2)+'\n')
F=json.loads((P/'verification/proof-freeze.json').read_text())
assert sha(P/'verification/proof-freeze.json')=='ab05e2bf801e6906453e88a4d84d5e73191f776db05610fb8b8e5e4a03d4f856'
for r,h in F['files'].items():assert sha(P/r)==h,r
record=json.loads((E/'fresh-checks.json').read_text())
assert len(record['commands'])==19
assert all(c['exit_code']==0 for c in record['commands'][:18])
assert record['commands'][18]['exit_code']==1
for c in record['commands'][:18]:
    for rel,h in c['fresh_objects'].items():assert sha(Path(record['fresh_prefix'])/rel)==h
m='reviews/final-referee-2-evidence/Inspect.lean'
cmd=[str(Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean')),m]
start=time.monotonic()
r=subprocess.run(cmd,cwd=P,env=dict(os.environ,LEAN_PATH=record['LEAN_PATH']),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
log=E/'Inspect-retry.log';log.write_bytes(r.stdout)
row={'source':m,'source_sha256':sha(P/m),'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-start,
 'log':log.name,'log_sha256':sha(log),'fresh_objects':{},'reason':'Only specify diagnostic Euclidean CLM index/scalar parameters; candidate objects reused from this independent fresh build'}
record['commands'].append(row)
save('fresh-checks.json',record)
print('Independent corrected inspector:',r.returncode,round(row['seconds'],3),'seconds',flush=True)
if r.returncode:
    print(r.stdout.decode()[-8000:],flush=True);raise SystemExit(r.returncode)
assert b'warning:' not in r.stdout and b'error:' not in r.stdout
axioms=[]
for c in [*record['commands'][:18],row]:
    for name,ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(E/c['log']).read_text()):
        aa=[a.strip() for a in ax.split(',') if a.strip()]
        assert set(aa)<={'propext','Classical.choice','Quot.sound'}
        axioms.append({'declaration':name,'axioms':aa,'log':c['log']})
assert len(axioms)==62,len(axioms)
save('axioms.json',{'result':'PASS','count':62,'standard_three_or_subset_only':True,'reports':axioms})
text=r.stdout.decode()
counts=re.findall(r'^REFEREE_COUNTS (\w+): project=(\d+), library=(\d+)',text,re.M)
required=re.findall(r'^REFEREE_REQUIRED (\w+): (\S+)',text,re.M)
assert len(counts)==2 and len(required)==82,(counts,len(required))
save('actual-proof-dependencies.json',{'result':'PASS','counts':counts,'required_per_closure':41,
 'final_target_separately_traversed':True,'actual_type_and_value_traversal':True,'required_consumed':required})
for rel,h in F['files'].items(): assert sha(P/rel)==h,rel
before=json.loads((E/'integrity-before.json').read_text())
for rel,h in F['source_files'].items():
    raw=subprocess.check_output(['git','-C',str(R),'show',F['base']+':'+rel])
    assert hashlib.sha256(raw).hexdigest()==h and (R/rel).read_bytes()==raw,rel
save('integrity-after.json',before)
pins=json.loads((E/'dependency-pins-before.json').read_text())
for pin in pins:
    args=['git','-C',pin['path']]
    assert subprocess.check_output(args+['rev-parse','HEAD']).decode().strip()==pin['revision']
    assert subprocess.check_output(args+['status','--porcelain=v1'])==b''
save('dependency-pins-after.json',pins)
record.update(result='PASS with one preserved reviewer-diagnostic CLM parameter correction',
  successful_commands=19,failed_reviewer_diagnostic_commands=1,
  completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
save('fresh-checks.json',record)
print(json.dumps({'result':'PASS','successful_commands':19,'preserved_inspector_failure':1,'axiom_reports':62,'closure_counts':counts}))
