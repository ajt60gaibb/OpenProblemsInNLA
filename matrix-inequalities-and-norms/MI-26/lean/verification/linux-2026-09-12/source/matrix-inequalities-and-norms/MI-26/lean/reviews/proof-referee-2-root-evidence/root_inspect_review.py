import hashlib, json, os, subprocess, sys, time
from pathlib import Path

project=Path(sys.argv[1]).resolve()
ref=sys.argv[2]
ev=project/'reviews'/f'proof-referee-{ref}-root-evidence'
execution=json.loads((ev/'execution.json').read_text())
assert all(x['exit_code']==0 for x in execution['commands'])
env=os.environ.copy()
env['LEAN_PATH']=execution['LEAN_PATH']
cmd=[execution['lean'],str((ev/'Inspect.lean').relative_to(project))]
start=time.monotonic()
r=subprocess.run(cmd,cwd=project,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(ev/'inspection.log').write_bytes(r.stdout)
record={'command':cmd,'exit_code':r.returncode,'elapsed_seconds':round(time.monotonic()-start,3),'log_sha256':hashlib.sha256(r.stdout).hexdigest(),'platform':'macOS arm64, using fresh referee prefix; not Linux Comparator'}
(ev/'inspection.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
assert r.returncode==0, r.stdout.decode(errors='replace')
assert b'warning:' not in r.stdout and b'error:' not in r.stdout
assert b'LeanCert.Validity.verify_strict_upper_bound_dyadic_checked' in r.stdout
packages=json.loads((project/'lake-manifest.json').read_text())['packages']
deps=[]
for p in packages:
    root=project/'.lake'/'packages'/p['name']
    actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
    dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=root,text=True)
    assert actual==p['rev'] and not dirty,(p['name'],actual,dirty)
    deps.append({'name':p['name'],'expected':p['rev'],'actual':actual,'tracked_sources_clean':True})
(ev/'dependencies.json').write_text(json.dumps({'status':'PASS','packages':deps},indent=2)+'\n')
print(json.dumps({'status':'PASS','clean_pinned_packages':len(deps)}),flush=True)
