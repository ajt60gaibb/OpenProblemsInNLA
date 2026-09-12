from pathlib import Path
import json,os,subprocess,time
repo=Path('/tmp/nla-lean-ra07-worktree')
pub=repo/'randomized-and-low-rank-approximation/RA-07/lean/verification/publication-2026-09-12'
commands=[
(['python3','tools/format_math.py','--write','RA-07'],'format-write.log'),
(['python3','tools/validate_problem_ids.py','--base-ref','origin/main'],'ids-origin-main.log'),
(['python3','tools/validate_problem_ids.py','--base-ref','nla-upstream/main'],'ids-upstream.log'),
(['python3','tools/update_catalog.py','--base-ref','origin/main'],'catalog.log'),
(['python3','-m','unittest','discover','-s','tests','-p','test_problem_ids.py','-v'],'id-tests.log'),
(['python3','tools/format_math.py','--check'],'format-check.log'),
(['/tmp/nla-lean-formalization/venv/bin/python','tools/lean/validate_manifest.py','randomized-and-low-rank-approximation/RA-07/lean'],'manifest.log'),
(['git','diff','--check'],'diff-check.log')]
results=[]
for cmd,name in commands:
 t=time.monotonic()
 with (pub/name).open('w') as f:p=subprocess.run(cmd,cwd=repo,stdout=f,stderr=subprocess.STDOUT)
 result={'command':cmd,'exit_code':p.returncode,'elapsed_seconds':round(time.monotonic()-t,3),'log':name}
 results.append(result);print(json.dumps(result),flush=True)
 assert p.returncode==0,name
(pub/'checks.json').write_text(json.dumps(results,indent=2)+'\n')
env=dict(os.environ,PANDOC='/tmp/nla-submission-tools/pandoc-3.11-arm64/bin/pandoc',XELATEX='/Library/TeX/texbin/xelatex')
cmd=['python3','tools/render_problems.py','RA-07'];t=time.monotonic()
with (pub/'render.log').open('w') as f:p=subprocess.run(cmd,cwd=repo,env=env,stdout=f,stderr=subprocess.STDOUT)
assert p.returncode==0,(pub/'render.log').read_text()
(pub/'render-result.json').write_text(json.dumps({'command':cmd,'exit_code':p.returncode,'elapsed_seconds':round(time.monotonic()-t,3),'pandoc':env['PANDOC'],'xelatex':env['XELATEX']},indent=2)+'\n')
print((pub/'render.log').read_text(),flush=True)
