#!/usr/bin/env python3
"""Check unchanged SP12 statement snapshots; implements no SP12 proof body."""
import argparse,pathlib,json,os,tempfile,subprocess,hashlib,platform
p=argparse.ArgumentParser(); p.add_argument('--dependency-root',type=pathlib.Path,required=True); p.add_argument('--lean-bin',type=pathlib.Path,required=True); a=p.parse_args()
e=pathlib.Path(__file__).resolve().parent; root=e/'sources/lean-statements'; out=pathlib.Path(tempfile.mkdtemp(prefix='sp12-statement-review2-'))
cache=a.dependency_root/'.lake/packages'; deps=[x/'.lake/build/lib/lean' for x in cache.iterdir() if (x/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,PATH=str(a.lean_bin)+':'+os.environ['PATH'],LEAN_PATH=':'.join(map(str,[out]+deps))); results=[]
for f in ['NLA/Statements/Infrastructure.lean','NLA/Statements/SP12.lean','Reviewed/SP12.lean']:
 s=root/f; before=hashlib.sha256(s.read_bytes()).hexdigest(); obj=out/pathlib.Path(f).with_suffix('.olean'); obj.parent.mkdir(parents=True,exist_ok=True); cmd=[str(a.lean_bin/'lean'),'-o',str(obj),f]; x=subprocess.run(cmd,cwd=root,env=env,capture_output=True,text=True); log=x.stdout+x.stderr; name=f.replace('/','_')+'.log'; (e/name).write_text(log); results.append(dict(source=f,source_sha256=before,unchanged=before==hashlib.sha256(s.read_bytes()).hexdigest(),command=cmd,exit_code=x.returncode,log=name,log_sha256=hashlib.sha256(log.encode()).hexdigest())); print(f,x.returncode,flush=True)
 if x.returncode: break
result=dict(reviewer='/root/solved_inventory',date='2026-10-18',scope='Preproof unchanged statement snapshot only. No SP12 proof body or Linux Comparator evidence.',platform=platform.platform(),isolated_output=str(out),shared_project_objects=False,commands=results,all_passed=len(results)==3 and all(x['exit_code']==0 and x['unchanged'] for x in results)); (e/'statement-build.json').write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result,indent=2)); raise SystemExit(0 if result['all_passed'] else 1)
