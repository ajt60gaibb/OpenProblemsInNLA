"""Fresh MF16 implementation-author source check, adapted from campaign IS03.
No local prior MF16 objects, Lake, cache copy, dependency build or Linux claim.
"""
from pathlib import Path
import datetime,hashlib,json,os,platform,re,subprocess,tempfile,time
P=Path(__file__).resolve().parents[2];E=Path(__file__).resolve().parent;W=P.parents[2]
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
L=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
freeze=json.loads((P/'reviews/statement-freeze.json').read_text())
def preserved():
 for rel,h in freeze['files'].items():assert sha(P/rel)==h,rel
 for rel,h in freeze['source_files'].items():
  data=subprocess.check_output(['git','-C',str(W),'show',freeze['base']+':'+rel])
  assert data==(W/rel).read_bytes() and hashlib.sha256(data).hexdigest()==h,rel
 assert not subprocess.check_output(['git','-C',str(W),'diff','--name-only'])
preserved();pins=[]
for row in json.loads((P/'lake-manifest.json').read_text())['packages']:
 d=C/row['name'];rev=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD']).decode().strip()
 assert rev==row['rev'] and not subprocess.check_output(['git','-C',str(d),'status','--porcelain=v1'])
 pins.append({'name':row['name'],'path':str(d.resolve()),'rev':rev,'clean':True})
run=Path(tempfile.mkdtemp(prefix='attempt-',dir=E))
prefix=Path(tempfile.mkdtemp(prefix='mf16-final-',dir='/tmp/nla-lean-formalization/independent-prefixes'))
order=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[prefix,*[C/n/'.lake/build/lib/lean' for n in order],L/'lib/lean']))
sources=['NLA/MF16/Definitions.lean','NLA/MF16/Numerical.lean','NLA/MF16/Algebra.lean',
 'NLA/MF16/Recovery.lean','NLA/MF16/Polynomial.lean','NLA/MF16/CayleyHamilton.lean',
 'NLA/MF16/Proof.lean','Solution.lean','verification/final/Inspect.lean','Challenge.lean']
record={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'platform':platform.platform(),
 'toolchain':subprocess.check_output([str(L/'bin/lean'),'--version']).decode().strip(),
 'scope':'Fresh local macOS source elaboration in initially empty project prefix. Every prior MF16 and MI22 project object excluded. Ten exact clean pinned dependency caches reused read-only; no dependency clone/copy/rebuild, Lake build, Linux or Comparator result.',
 'prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],'pins':pins,'commands':[]}
for rel in sources:
 p=P/rel;target=prefix/Path(rel).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
 (run/(rel.replace('/','-')+'.txt')).write_bytes(p.read_bytes())
 cmd=[str(L/'bin/lean'),'-o',str(target),'-i',str(target.with_suffix('.ilean')),str(p)]
 start=time.monotonic();r=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
 output=r.stdout+r.stderr;log=run/(rel.replace('/','-').replace('.lean','.log'));log.write_bytes(output)
 row={'source':rel,'sha256':sha(p),'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-start,'log':log.name,'log_sha256':sha(log)}
 record['commands'].append(row);(run/'result.json').write_text(json.dumps(record,indent=2)+'\n')
 print(rel,r.returncode,round(row['seconds'],2),flush=True)
 if r.returncode:
  print(output.decode()[:15000],flush=True);raise SystemExit(r.returncode)
 if rel=='Challenge.lean':assert output.decode().count('warning: declaration uses `sorry`')==9
 else:assert 'warning:' not in output.decode() and 'error:' not in output.decode(),log
 for closure in re.findall(r'depends on axioms: \[(.*?)\]',output.decode(),re.S):
  assert {x.strip() for x in closure.split(',')} <= {'propext','Classical.choice','Quot.sound'},closure
for row in pins:
 assert subprocess.check_output(['git','-C',row['path'],'rev-parse','HEAD']).decode().strip()==row['rev']
 assert not subprocess.check_output(['git','-C',row['path'],'status','--porcelain=v1'])
preserved()
record.update({'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verdict':'PASS full fresh local implementation and actual dependency inspection','frozen_inputs_preserved':len(freeze['files']),'original_Git_sources_preserved':len(freeze['source_files']),'pins_rechecked_after':True})
(run/'result.json').write_text(json.dumps(record,indent=2)+'\n')
(E/'latest.json').write_text(json.dumps({'attempt':str(run),'prefix':str(prefix),'result_sha256':sha(run/'result.json')},indent=2)+'\n')
print('PASS',run,flush=True)
