"""One evolving MF16 Cayley-Hamilton helper development prefix; no Lake or dependency mutation."""
from pathlib import Path
import os,sys,json,hashlib,subprocess,tempfile,datetime,time
P=Path(__file__).resolve().parents[2];E=Path(__file__).resolve().parent
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean')
L=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
f=json.loads((P/'reviews/statement-freeze.json').read_text())
for r,h in f['files'].items():assert sha(P/r)==h,r
assert (E/'gate-acknowledged.json').exists()
state=E/'prefix.json'
if state.exists():prefix=Path(json.loads(state.read_text())['path'])
else:
 prefix=Path(tempfile.mkdtemp(prefix='mf16-cayley-hamilton-',dir='/tmp/nla-lean-formalization/independent-prefixes'))
 state.write_text(json.dumps({'path':str(prefix),'note':'One evolving development prefix, excluded from later fresh review prefixes.'},indent=2)+'\n')
order=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
pins=json.loads((P/'lake-manifest.json').read_text())['packages'];pinrecords=[]
for row in pins:
 dep=C/'.lake/packages'/row['name'];rev=subprocess.check_output(['git','-C',str(dep),'rev-parse','HEAD']).decode().strip()
 assert rev==row['rev'] and not subprocess.check_output(['git','-C',str(dep),'status','--porcelain=v1'])
 pinrecords.append({'name':row['name'],'path':str(dep),'revision':rev,'clean':True})
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[prefix,*[C/'.lake/packages'/p/'.lake/build/lib/lean' for p in order],L/'lib/lean']))
attempt=Path(tempfile.mkdtemp(prefix='attempt-',dir=E))
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],'dependency_mode':'Ten exact pinned MI22 sources/compiled dependencies read-only; no dependency download, build or copy. This is development, not final fresh review or Linux.','pins':pinrecords,'commands':[]}
for rel in sys.argv[1:]:
 source=P/rel;target=prefix/Path(rel).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
 (attempt/(rel.replace('/','-')+'.txt')).write_bytes(source.read_bytes())
 cmd=[str(L/'bin/lean'),'-o',str(target),'-i',str(target.with_suffix('.ilean')),str(source)]
 start=time.monotonic();r=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
 log=attempt/(rel.replace('/','-')+'.log');log.write_bytes(r.stdout+r.stderr)
 record['commands'].append({'source':rel,'sha256':sha(source),'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-start,'log':log.name,'log_sha256':sha(log)})
 (attempt/'result.json').write_text(json.dumps(record,indent=2)+'\n')
 print(rel,r.returncode,round(time.monotonic()-start,2),flush=True)
 print(log.read_text()[:14000],flush=True)
 if r.returncode:raise SystemExit(r.returncode)
print('PASS',attempt,flush=True)
