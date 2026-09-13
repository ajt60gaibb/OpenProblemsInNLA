"""Run only metadata and permanent-ID checks for the RA-08 Linux candidate.

No proof/dependency build or mutation is performed. Independent read-only
validators run concurrently; their actual outputs and return codes are saved.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import datetime, hashlib, json, os, subprocess, time

E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
python='/tmp/nla-lean-formalization/venv/bin/python'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
jobs=[('manifest.log',[python,'tools/lean/validate_manifest.py',str(P)]),
      ('permanent-ids-origin.log',[python,'tools/validate_problem_ids.py','--base-ref','origin/main']),
      ('permanent-ids-upstream.log',[python,'tools/validate_problem_ids.py','--base-ref','nla-upstream/main'])]
env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
def run(job):
    name,argv=job;start=time.monotonic()
    result=subprocess.run(argv,cwd=W,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
    (E/name).write_text(result.stdout)
    return {'argv':argv,'cwd':str(W),'seconds':time.monotonic()-start,'exit_code':result.returncode,
            'log':name,'log_sha256':sha(E/name)}
with ThreadPoolExecutor(max_workers=3) as pool:commands=list(pool.map(run,jobs))
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'commands':commands,'all_exit_zero':all(r['exit_code']==0 for r in commands),
        'validator_inputs':{n:sha(W/n) for n in ['tools/lean/validate_manifest.py','docs/lean/schema/v0.4.schema.json','tools/validate_problem_ids.py']},
        'live_wrappers':{n:sha(P/n) for n in ['README.md','formalization.yaml']},
        'base_refs':{n:subprocess.check_output(['git','rev-parse',n],cwd=W,text=True).strip() for n in ['HEAD','origin/main','nla-upstream/main']},
        'proof_and_dependency_checks_performed':False,'source_status_git_mutations':False}
(E/'validation-checks.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
assert record['all_exit_zero']
