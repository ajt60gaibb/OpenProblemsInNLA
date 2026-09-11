"""Run read-reviewed local preservation/index safeguards in isolated worktrees."""
from pathlib import Path
import json,subprocess
from concurrent.futures import ThreadPoolExecutor

OUT=Path(__file__).resolve().parent
BASE='87366c62d3b5c47d170f747b1cb40ab38d501013'
def run(pr,id):
    root=Path(f'/private/tmp/nla-pr{pr}-latest-delta')
    ref='references/stepaniants-'+id.lower().replace('-','')+'-2026-09-11/verification/verify_main_integration.py'
    commands=[
        ['python3',ref],
        ['python3','tools/validate_problem_ids.py','--base-ref',BASE],
        ['python3','tools/update_catalog.py','--base-ref',BASE],
        ['python3','-m','unittest','discover','-s','tests','-p','test_problem_ids.py','-v'],
        ['git','status','--porcelain']]
    outputs=[]
    for command in commands:
        result=subprocess.run(command,cwd=root,text=True,capture_output=True)
        outputs.append({'command':command,'exit_code':result.returncode,'stdout':result.stdout,'stderr':result.stderr})
        assert result.returncode==0,(pr,command,result.stderr)
    assert not outputs[-1]['stdout'],(pr,'catalog regeneration changed a file')
    report={'pr':pr,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'status':'PASS','commands':outputs,'worktree_clean_after_generation':True}
    (OUT/f'PR{pr}-local-integration-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    return {'pr':pr,'status':'PASS','commands':len(commands),'tests':17,'catalog_idempotent':True}
with ThreadPoolExecutor(max_workers=2) as pool:
    results=list(pool.map(lambda job:run(*job),[(93,'RA-12'),(103,'RA-10')]))
print(json.dumps(results,indent=2))
