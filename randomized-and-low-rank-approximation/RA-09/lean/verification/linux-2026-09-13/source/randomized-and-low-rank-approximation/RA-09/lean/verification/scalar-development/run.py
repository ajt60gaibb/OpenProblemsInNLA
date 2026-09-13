"""Direct-source scalar development, one evolving prefix; no old project objects.
All attempts retain exact source bytes and raw output. Read-only MI22 dependencies.
"""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,tempfile,time
E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
L=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(P/'verification/proof-start.json')=='1838ba4734f82970700086ef9850cea848ffa7f72b52055e89b94d2a19678b8e'
assert sha(P/'verification/implementation-roles.json')=='6949645a1f5d5e139aa31014017df2990e23856ddfdd9377f7df520c7a5cf385'
f=json.loads((P/'reviews/statement-freeze.json').read_text())
for name,h in f['files'].items():assert sha(P/name)==h,name
for name,h in f['source_files'].items():assert sha(W/name)==h,name
pins=[]
for dep in json.loads((P/'lake-manifest.json').read_text())['packages']:
    q=C/dep['name'];rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=q).decode().strip()
    assert rev==dep['rev'] and not subprocess.check_output(['git','status','--porcelain=v1'],cwd=q)
    pins.append({'name':dep['name'],'rev':rev,'git_clean':True,'path':str(q)})
statepath=E/'development-state.json'
if statepath.exists():
    state=json.loads(statepath.read_text());prefix=Path(state['prefix']);assert prefix.is_dir()
else:
    prefix=Path(tempfile.mkdtemp(prefix='ra09-scalar-',dir='/tmp/nla-lean-formalization/independent-prefixes'))
    state={'prefix':str(prefix),'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'owner':'/root/formal_review_standards','initially_empty':True,'pins':pins}
    statepath.write_text(json.dumps(state,indent=2)+'\n')
order=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[prefix,*[C/n/'.lake/build/lib/lean' for n in order],L/'lib/lean']))
attempt=Path(tempfile.mkdtemp(prefix='attempt-',dir=E))
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Evolving helper development on macOS, not fresh final/Linux verification.',
 'prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],'pins':pins,'commands':[]}
sources=[]
if not(prefix/'NLA/RA09/Definitions.olean').exists():sources.append('NLA/RA09/Definitions.lean')
sources.append('NLA/RA09/Scalar.lean')
for name in sources:
    source=P/name;target=prefix/Path(name).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
    (attempt/(name.replace('/','-')+'.txt')).write_bytes(source.read_bytes())
    cmd=[str(L/'bin/lean'),'-o',str(target),'-i',str(target.with_suffix('.ilean')),str(source)]
    start=time.monotonic();r=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
    log=attempt/name.replace('/','-').replace('.lean','.log');log.write_bytes(r.stdout+r.stderr)
    row={'source':name,'source_sha256':sha(source),'command':cmd,'exit_code':r.returncode,
     'seconds':time.monotonic()-start,'log':log.name,'log_sha256':sha(log)}
    record['commands'].append(row);(attempt/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    print(name,r.returncode,round(row['seconds'],2),flush=True)
    if r.returncode:print(log.read_text()[-14000:],flush=True);break
for name,h in f['files'].items():assert sha(P/name)==h,name
record['all_31_frozen_project_inputs_preserved']=True
record['result']='PASS' if all(x['exit_code']==0 for x in record['commands']) else 'FAIL'
(attempt/'result.json').write_text(json.dumps(record,indent=2)+'\n')
(E/'latest.json').write_text(json.dumps({'attempt':str(attempt),'result_sha256':sha(attempt/'result.json')},indent=2)+'\n')
print(attempt,record['result'],flush=True)
raise SystemExit(0 if record['result']=='PASS' else 1)
