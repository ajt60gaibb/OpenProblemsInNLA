"""Fresh local IV06 author builds. Reads the ten pinned MI22 caches only."""
from pathlib import Path
import datetime,hashlib,json,os,platform,subprocess,tempfile,time
P=Path(__file__).resolve().parents[2]
E=Path(__file__).resolve().parent
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean')
L=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
manifest=json.loads((P/'lake-manifest.json').read_text());pins=[]
for package in manifest['packages']:
 dep=C/'.lake/packages'/package['name']
 rev=subprocess.check_output(['git','-C',str(dep),'rev-parse','HEAD']).decode().strip()
 status=subprocess.check_output(['git','-C',str(dep),'status','--porcelain=v1'])
 assert rev==package['rev'] and not status,(dep,rev,status)
 pins.append({'name':package['name'],'path':str(dep.resolve()),'expected':package['rev'],'actual':rev,'git_clean':True})
run=Path(tempfile.mkdtemp(prefix='attempt-',dir=E))
prefix=Path(tempfile.mkdtemp(prefix='iv06-proof-',dir='/tmp/nla-lean-formalization/independent-prefixes'))
order=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
paths=[prefix,*[(C/'.lake/packages'/n/'.lake/build/lib/lean').resolve() for n in order],L/'lib/lean']
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,paths))
record={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'platform':platform.platform(),'scope':'Fresh local macOS IV06 source elaboration; ten exact clean dependencies reused read-only; no Lake rebuild or Linux Comparator claim','fresh_prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],'pins':pins,'commands':[]}
for source in ['NLA/IV06/Definitions.lean','NLA/IV06/Proof.lean','Solution.lean']:
 sourcefile=P/source
 (run/(source.replace('/','-')+'.txt')).write_bytes(sourcefile.read_bytes())
 target=prefix/Path(source).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
 cmd=[str(L/'bin/lean'),'-o',str(target),'-i',str(target.with_suffix('.ilean')),str(sourcefile)]
 t=time.monotonic();res=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
 log=run/(source.replace('/','-').replace('.lean','.log'));log.write_bytes(res.stdout+res.stderr)
 row={'source':source,'source_sha256':sha(sourcefile),'command':cmd,'exit_code':res.returncode,'seconds':time.monotonic()-t,'log':log.name,'log_sha256':sha(log)}
 record['commands'].append(row);(run/'result.json').write_text(json.dumps(record,indent=2)+'\n')
 print(source,res.returncode,round(row['seconds'],2),flush=True)
 if res.returncode:
  print(log.read_text(),flush=True);raise SystemExit(res.returncode)
record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();record['verdict']='PASS'
(run/'result.json').write_text(json.dumps(record,indent=2)+'\n')
(E/'latest.json').write_text(json.dumps({'attempt':str(run),'fresh_prefix':str(prefix),'result_sha256':sha(run/'result.json')},indent=2)+'\n')
print('PASS',run,flush=True)
