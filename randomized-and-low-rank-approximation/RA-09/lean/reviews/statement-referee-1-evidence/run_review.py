from pathlib import Path
import os,json,hashlib,subprocess,tempfile,datetime,time,re,sys
P=Path(__file__).resolve().parents[2];E=Path(__file__).resolve().parent;R=P.parents[2]
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean')
L=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=json.loads((P/'reviews/statement-freeze.json').read_text())
assert sha(P/'reviews/statement-freeze.json')=='c144b68990fca06c554790b25bfaef7544c0a8baf532e5b38365fe74ee9c87ed'
def integrity():
 for r,h in f['files'].items():assert sha(P/r)==h,r
 for r,h in f['source_files'].items():
  assert sha(R/r)==h,r
  assert hashlib.sha256(subprocess.check_output(['git','-C',str(R),'show',f['base']+':'+r])).hexdigest()==h,r
 assert not (P/'Solution.lean').exists()
 assert not (P/'NLA/RA09/Proof.lean').exists()
 return {'frozen_project_inputs':len(f['files']),'original_Git_inputs':len(f['source_files']),'all_unchanged':True,'implementation_absent':True}
def pins():
 rows=[]
 for p in json.loads((P/'lake-manifest.json').read_text())['packages']:
  d=C/'.lake/packages'/p['name'];rev=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD']).decode().strip()
  assert rev==p['rev']
  assert not subprocess.check_output(['git','-C',str(d),'status','--porcelain=v1'])
  rows.append({'name':p['name'],'path':str(d),'revision':rev,'clean':True})
 return rows
before={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':integrity(),'pins':pins()}
(E/'before.json').write_text(json.dumps(before,indent=2)+'\n')
prefix=Path(tempfile.mkdtemp(prefix='ra09-root-statements-',dir='/tmp/nla-lean-formalization/independent-prefixes'))
order=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[prefix,*[C/'.lake/packages'/p/'.lake/build/lib/lean' for p in order],L/'lib/lean']))
record={'utc':before['utc'],'platform':'macOS local direct-source statement inspection, not a proof implementation or Linux/Comparator run','prefix':str(prefix),'initial_prefix_empty':not any(prefix.rglob('*')),'LEAN_PATH':env['LEAN_PATH'],'dependency_policy':'Ten exact clean matching MI22 dependency objects read-only. No project object, cache copy/download or Lake invocation.','commands':[]}
for rel in ['NLA/RA09/Definitions.lean','Challenge.lean','reviews/statement-referee-1-evidence/Inspect.lean']:
 src=P/rel;out=prefix/Path(rel).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 snap=E/(rel.replace('/','-')+'.txt');snap.write_bytes(src.read_bytes())
 cmd=[str(L/'bin/lean'),'-o',str(out),'-i',str(out.with_suffix('.ilean')),str(src)]
 t=time.monotonic();r=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
 log=E/(rel.replace('/','-')+'.log');log.write_bytes(r.stdout+r.stderr)
 entry={'source':rel,'sha256':sha(src),'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-t,'log':log.name,'log_sha256':sha(log)}
 record['commands'].append(entry);(E/'fresh-checks.json').write_text(json.dumps(record,indent=2)+'\n')
 print(rel,r.returncode,round(entry['seconds'],2),flush=True)
 if r.returncode:
  print(log.read_text(),flush=True);raise SystemExit(r.returncode)
 if rel=='Challenge.lean':assert log.read_text().count("warning: declaration uses \u0060sorry\u0060")==17
 else:assert 'warning:' not in log.read_text() and 'error:' not in log.read_text()
text=(E/'reviews-statement-referee-1-evidence-Inspect.lean.log').read_text()
assert 'Matrix.frobeniusNormedAddCommGroup' in text and '@cfc' in text
reports=[line for line in text.splitlines() if 'depends on axioms:' in line]
assert len(reports)==17
assert all('[propext, Classical.choice, Quot.sound]' in line for line in reports)
(E/'after.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':integrity(),'pins':pins(),'structural_standard_three_reports':reports,'actual_frobenius_instance':'Matrix.frobeniusNormedAddCommGroup','actual_cfc':'@cfc present in elaborated body','note':'These are structural statement checks, not proofs of the seventeen Challenge obligations.'},indent=2)+'\n')
print('PASS three fresh statement checks,17intentional placeholders,17structural kernel/std3 reports; all31+17 unchanged',flush=True)
