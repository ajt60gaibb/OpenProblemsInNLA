"""Independent MI-23 statement elaboration, with project artifact cache excluded."""
from pathlib import Path
import os, subprocess, json, hashlib, time
PROJECT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
ART=PROJECT/'.verification/statement-referee-1'
ART.mkdir(parents=True,exist_ok=True)
LEAN=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean')
LAKE=LEAN.with_name('lake')
raw=subprocess.check_output([str(LAKE),'env','printenv','LEAN_PATH'],cwd=PROJECT).decode().strip()
parts=[s for s in raw.split(os.pathsep) if Path(s).resolve() != (PROJECT/'.lake/build/lib/lean').resolve()]
assert all(Path(s).resolve() != (PROJECT/'.lake/build/lib/lean').resolve() for s in parts)
env=dict(os.environ)
env['LEAN_PATH']=os.pathsep.join([str(ART)]+parts)
commands=[]
for source,output,log in [('NLA/MI23/Definitions.lean','NLA/MI23/Definitions.olean','definitions.log'),('Challenge.lean','Challenge.olean','challenge.log'),('reviews/statement-referee-1-evidence/Inspect.lean',None,'inspection.log')]:
 cmd=[str(LEAN)]
 if output:
  target=ART/output;target.parent.mkdir(parents=True,exist_ok=True)
  assert not target.exists(),'Referee prefix must be fresh'
  cmd += ['-o',str(target)]
 cmd += [source]
 start=time.monotonic();r=subprocess.run(cmd,cwd=PROJECT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/log).write_bytes(r.stdout)
 commands.append({'command':cmd,'exit_code':r.returncode,'elapsed_seconds':round(time.monotonic()-start,3),'log':log,'log_sha256':hashlib.sha256(r.stdout).hexdigest()})
 (OUT/'fresh-checks.json').write_text(json.dumps({'platform':'macOS arm64; local fresh statement elaboration only','LEAN_PATH':env['LEAN_PATH'],'original_project_artifacts_excluded':True,'commands':commands},indent=2)+'\n')
 print(source,'exit',r.returncode,flush=True)
 if r.returncode:print(r.stdout.decode());raise SystemExit(r.returncode)
assert (OUT/'definitions.log').read_text()==''
assert (OUT/'challenge.log').read_text().count('declaration uses `sorry`')==8
assert 'warning:' not in (OUT/'inspection.log').read_text()
print('PASS: fresh Definitions, Challenge and actual semantics inspection; eight deliberate Challenge holes only.')
