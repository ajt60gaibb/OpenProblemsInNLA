#!/usr/bin/env python3
"""Fresh local source check of this complete canonical package.

Uses only pinned cached dependency objects; no shared NLA project objects.
This does not perform the separate authoritative Linux Comparator run.
"""
import argparse, hashlib, json, os, pathlib, platform, re, subprocess, tempfile, time
p=argparse.ArgumentParser(); p.add_argument('--dependency-root',type=pathlib.Path,required=True); p.add_argument('--lean-bin',type=pathlib.Path,required=True); p.add_argument('--output',type=pathlib.Path,required=True); a=p.parse_args()
project=pathlib.Path(__file__).resolve().parents[1]; repo=project.parents[2]
a.output.mkdir(parents=True,exist_ok=True)
cache=a.dependency_root/'.lake/packages'
manifest=json.loads((project/'lake-manifest.json').read_text()); depchecks=[]
for d in manifest['packages']:
    actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=cache/d['name'],text=True).strip()
    depchecks.append(dict(package=d['name'],expected=d['rev'],actual=actual,matched=actual==d['rev']))
if not all(x['matched'] for x in depchecks): raise RuntimeError('Dependency revision mismatch')
deps=[x/'.lake/build/lib/lean' for x in cache.iterdir() if (x/'.lake/build/lib/lean').is_dir()]
out=pathlib.Path(tempfile.mkdtemp(prefix='sp11-complete-package-fresh-'))
env=dict(os.environ,PATH=str(a.lean_bin)+':'+os.environ['PATH'],LEAN_PATH=':'.join(map(str,[out]+deps)))
order=[]; seen=set()
def visit(module):
    if module in seen: return
    seen.add(module); file=project/pathlib.Path(*module.split('.')).with_suffix('.lean')
    if not file.is_file(): raise RuntimeError('Missing project source: '+module)
    for line in file.read_text().splitlines():
        if line.startswith('import '):
            for child in line.split()[1:]:
                if child.startswith(('NLA.','Reviewed.')): visit(child)
    order.append(module)
for entry in ['Solution','Identity','Challenge']: visit(entry)
records=[]
for module in order:
    rel=pathlib.Path(*module.split('.')).with_suffix('.lean'); src=project/rel; before=hashlib.sha256(src.read_bytes()).hexdigest()
    obj=out/rel.with_suffix('.olean'); obj.parent.mkdir(parents=True,exist_ok=True)
    cmd=[str(a.lean_bin/'lean'),'-o',str(obj),str(rel)]; start=time.monotonic()
    run=subprocess.run(cmd,cwd=project,env=env,capture_output=True,text=True)
    log=run.stdout+run.stderr; logname=module+'.log'; (a.output/logname).write_text(log)
    records.append(dict(module=module,source=str(rel),source_sha256=before,source_unchanged_during_run=before==hashlib.sha256(src.read_bytes()).hexdigest(),command=cmd,exit_code=run.returncode,elapsed_seconds=round(time.monotonic()-start,3),log=logname,log_sha256=hashlib.sha256(log.encode()).hexdigest()))
    print(str(len(records))+'/'+str(len(order))+' '+module+' exit='+str(run.returncode),flush=True)
    if run.returncode: break
lock=json.loads((project/'proof-source-lock.json').read_text()); copychecks=[]
for x in lock['copies']:
    src=repo/x['source']; dest=repo/x['destination']
    sh=hashlib.sha256(src.read_bytes()).hexdigest(); dh=hashlib.sha256(dest.read_bytes()).hexdigest()
    copychecks.append(dict(module=x['module'],matched=sh==dh==x['source_sha256']==x['destination_sha256'],source_sha256=sh,destination_sha256=dh))
exports={f:hashlib.sha256((project/f).read_bytes()).hexdigest() for f in lock['package_exports']}
passed=len(records)==len(order) and all(x['exit_code']==0 and x['source_unchanged_during_run'] for x in records) and all(x['matched'] for x in copychecks) and exports==lock['package_exports']
result=dict(date='2026-10-18',author='/root/solved_inventory',scope='Fresh complete canonical source check using isolated NLA objects and pinned cached dependencies. Not Linux Comparator evidence or an independent review of author-owned modules.',platform=platform.platform(),isolated_output=str(out),lean_path_includes_shared_project_outputs=False,dependencies=depchecks,module_count=len(order),proof_module_count=sum(m.startswith('NLA.Proofs.') for m in order),commands=records,copy_checks=copychecks,package_exports=exports,all_passed=passed,challenge_sorry_expected=True)
(a.output/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['commands','copy_checks','dependencies']},indent=2)); raise SystemExit(0 if passed else 1)
