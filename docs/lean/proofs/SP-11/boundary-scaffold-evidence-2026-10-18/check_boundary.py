#!/usr/bin/env python3
"""Freshly typecheck only the frozen SP-11 boundary, using pinned cached dependencies.

Usage: python3 check_boundary.py --root /absolute/repository --dependency-root /absolute/lean-statements
This does not materialize dependencies or perform Linux Comparator verification.
"""
import argparse, hashlib, json, os, pathlib, platform, subprocess, tempfile, time
p=argparse.ArgumentParser(); p.add_argument('--root',type=pathlib.Path,required=True); p.add_argument('--dependency-root',type=pathlib.Path,required=True); p.add_argument('--lean-bin',type=pathlib.Path,required=True); a=p.parse_args()
project=a.root/'eigenvalues-and-inverse-problems/SP-11/lean'
cache=a.dependency_root/'.lake/packages'
deps=[x/'.lake/build/lib/lean' for x in cache.iterdir() if (x/'.lake/build/lib/lean').is_dir()]
out=pathlib.Path(tempfile.mkdtemp(prefix='sp11-boundary-fresh-'))
env=dict(os.environ,PATH=str(a.lean_bin)+':'+os.environ['PATH'],LEAN_PATH=':'.join(map(str,[out]+deps)))
evidence=pathlib.Path(__file__).resolve().parent
records=[]
for file in ['NLA/Statements/Infrastructure.lean','NLA/Statements/SP11.lean','Reviewed/SP11.lean','Identity.lean','Challenge.lean']:
    src=project/file; before=hashlib.sha256(src.read_bytes()).hexdigest()
    obj=out/pathlib.Path(file).with_suffix('.olean'); obj.parent.mkdir(parents=True,exist_ok=True)
    cmd=[str(a.lean_bin/'lean'),'-o',str(obj),file]
    start=time.monotonic(); run=subprocess.run(cmd,cwd=project,env=env,capture_output=True,text=True)
    log=run.stdout+run.stderr; logname=file.replace('/','_')+'.log'; (evidence/logname).write_text(log)
    records.append(dict(source=file,source_sha256=before,source_unchanged_during_run=before==hashlib.sha256(src.read_bytes()).hexdigest(),command=cmd,exit_code=run.returncode,elapsed_seconds=round(time.monotonic()-start,3),log=logname,log_sha256=hashlib.sha256(log.encode()).hexdigest()))
    if run.returncode: break
lock=json.loads((project/'boundary-source-lock.json').read_text())
copy_checks=[dict(package_path=x['package_path'],same_as_shared=(project/x['package_path']).read_bytes()==(a.root/x['shared_source']).read_bytes(),sha256=hashlib.sha256((project/x['package_path']).read_bytes()).hexdigest(),expected=x['sha256']) for x in lock['copied_sources']]
result=dict(date='2026-10-18',reviewer='/root/solved_inventory',scope='Boundary only: exact statement definitions, their definitional identity, and deliberate Challenge placeholder. No Target proof or Comparator acceptance.',platform=platform.platform(),isolated_own_output=str(out),lean_path_includes_shared_project_outputs=False,dependencies_from=str(cache),commands=records,copy_checks=copy_checks,all_passed=len(records)==5 and all(x['exit_code']==0 and x['source_unchanged_during_run'] for x in records) and all(x['same_as_shared'] and x['sha256']==x['expected'] for x in copy_checks),challenge_sorry_expected=True)
(evidence/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2)); raise SystemExit(0 if result['all_passed'] else 1)
