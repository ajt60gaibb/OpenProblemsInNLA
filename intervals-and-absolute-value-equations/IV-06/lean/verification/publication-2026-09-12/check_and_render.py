from pathlib import Path
import hashlib, json, os, subprocess

repo = Path('/tmp/nla-lean-iv06-worktree')
pub = repo/'intervals-and-absolute-value-equations/IV-06/lean/verification/publication-2026-09-12'
env = os.environ.copy()
env['PANDOC'] = '/tmp/nla-submission-tools/pandoc-3.11-arm64/bin/pandoc'
env['XELATEX'] = '/Library/TeX/texbin/xelatex'
commands = [
    ('permanent-ids-origin',['python3','tools/validate_problem_ids.py','--base-ref','origin/main']),
    ('permanent-ids-upstream',['python3','tools/validate_problem_ids.py','--base-ref','nla-upstream/main']),
    ('manifest',['/tmp/nla-lean-formalization/venv/bin/python','tools/lean/validate_manifest.py','intervals-and-absolute-value-equations/IV-06/lean']),
    ('format-write',['python3','tools/format_math.py','--write','IV-06']),
    ('catalog',['python3','tools/update_catalog.py','--base-ref','origin/main']),
    ('permanent-id-tests',['python3','-m','unittest','discover','-s','tests','-p','test_problem_ids.py','-v']),
    ('format-check',['python3','tools/format_math.py','--check']),
    ('render',['python3','tools/render_problems.py','IV-06']),
    ('pdfinfo',['/opt/homebrew/bin/pdfinfo','intervals-and-absolute-value-equations/IV-06/problem.pdf']),
]
checks = []
for name,args in commands:
    r = subprocess.run(args,cwd=repo,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (pub/(name+'.log')).write_bytes(r.stdout)
    checks.append({'name':name,'command':args,'exit_code':r.returncode,'log':name+'.log','log_sha256':hashlib.sha256(r.stdout).hexdigest()})
    print(name,'exit',r.returncode,r.stdout.decode()[-1500:],flush=True)
    (pub/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
    assert r.returncode == 0, name
(pub/'check_and_render.py').write_bytes(Path(__file__).read_bytes())
