from pathlib import Path
import os,subprocess,json,hashlib
repo=Path('/tmp/nla-lean-fr12-worktree');pub=repo/'frames-and-matrix-designs/FR-12/lean/verification/publication-2026-09-12'
checks=[{'name':'permanent-ids-origin','command':['python3','tools/validate_problem_ids.py','--base-ref','origin/main'],'exit_code':0,'output':'Validated 217 permanent problem IDs against origin/main\n','capture':'Actual preceding exec_command tool result'}, {'name':'permanent-ids-upstream','command':['python3','tools/validate_problem_ids.py','--base-ref','nla-upstream/main'],'exit_code':0,'output':'Validated 217 permanent problem IDs against nla-upstream/main\n','capture':'Actual preceding exec_command tool result'}, {'name':'manifest','command':['/tmp/nla-lean-formalization/venv/bin/python','tools/lean/validate_manifest.py','frames-and-matrix-designs/FR-12/lean'],'exit_code':0,'output':'Manifest schema and comparator coverage: PASS (7 declarations)\n','capture':'Actual preceding exec_command tool result'}]
env=os.environ.copy();env['PANDOC']='/tmp/nla-submission-tools/pandoc-3.11-arm64/bin/pandoc';env['XELATEX']='/Library/TeX/texbin/xelatex'
commands=[('format-write',['python3','tools/format_math.py','--write','FR-12']),('catalog',['python3','tools/update_catalog.py','--base-ref','origin/main']),('permanent-id-tests',['python3','-m','unittest','discover','-s','tests','-p','test_problem_ids.py','-v']),('format-check',['python3','tools/format_math.py','--check']),('render',['python3','tools/render_problems.py','FR-12']),('pdfinfo',['pdfinfo','frames-and-matrix-designs/FR-12/problem.pdf'])]
for name,args in commands:
 r=subprocess.run(args,cwd=repo,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(pub/(name+'.log')).write_bytes(r.stdout)
 checks.append({'name':name,'command':args,'exit_code':r.returncode,'log':name+'.log','log_sha256':hashlib.sha256(r.stdout).hexdigest()})
 print(name,'exit',r.returncode,r.stdout.decode()[-600:],flush=True)
 (pub/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
 assert r.returncode==0,name
(pub/'check_and_render.py').write_bytes(Path(__file__).read_bytes())
