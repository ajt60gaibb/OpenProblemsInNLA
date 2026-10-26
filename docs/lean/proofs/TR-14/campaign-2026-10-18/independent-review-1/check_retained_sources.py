#!/usr/bin/env python3
"""Read-only replay of retained TR14 sources; implements no proof bodies."""
import argparse,pathlib,json,os,hashlib,subprocess,tempfile,platform,time
p=argparse.ArgumentParser();p.add_argument('--dependency-root',type=pathlib.Path,required=True);p.add_argument('--lean-bin',type=pathlib.Path,required=True);a=p.parse_args();e=pathlib.Path(__file__).resolve().parent;root=e/'sources/lean-statements';cache=a.dependency_root/'.lake/packages';out=pathlib.Path(tempfile.mkdtemp(prefix='tr14-retained-review1-'));env=dict(os.environ,PATH=str(a.lean_bin)+':'+os.environ['PATH'],LEAN_PATH=':'.join(map(str,[out]+[x/'.lake/build/lib/lean' for x in cache.iterdir() if (x/'.lake/build/lib/lean').is_dir()])));seen=set();order=[]
def visit(m):
 if m in seen:return
 seen.add(m);s=root/pathlib.Path(*m.split('.')).with_suffix('.lean');assert s.is_file(),m
 for l in s.read_text().splitlines():
  if l.startswith('import '):
   for c in l.split()[1:]:
    if c.startswith(('NLA.','Reviewed.')):visit(c)
 order.append(m)
for s in sorted((root/'NLA/Proofs/TR14').glob('*.lean')):visit('NLA.Proofs.TR14.'+s.stem)
visit('Reviewed.TR14');results=[]
for m in order:
 f=pathlib.Path(*m.split('.')).with_suffix('.lean');s=root/f;before=hashlib.sha256(s.read_bytes()).hexdigest();obj=out/f.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);cmd=[str(a.lean_bin/'lean'),'-o',str(obj),str(f)];t=time.monotonic();x=subprocess.run(cmd,cwd=root,env=env,capture_output=True,text=True);log=x.stdout+x.stderr;(e/(m+'.log')).write_text(log);results.append(dict(module=m,source_sha256=before,unchanged_during_run=before==hashlib.sha256(s.read_bytes()).hexdigest(),command=cmd,exit_code=x.returncode,seconds=round(time.monotonic()-t,3),log=m+'.log',log_sha256=hashlib.sha256(log.encode()).hexdigest()));print(str(len(results))+'/'+str(len(order)),m,x.returncode,flush=True)
 if x.returncode:break
z=dict(date='2026-10-18',reviewer='/root/solved_inventory',scope='Retained39module candidate source replay and unchanged statement check, no new proof bodies/fullTarget/Comparator assertion. Source semantic approval is limited to preproof statement fidelity and gap audit.',platform=platform.platform(),isolated_output=str(out),shared_project_objects=False,module_count=len(order),commands=results,all_passed=len(results)==len(order) and all(x['exit_code']==0 and x['unchanged_during_run'] for x in results));(e/'retained-build.json').write_text(json.dumps(z,indent=2)+'\n');print(json.dumps({k:v for k,v in z.items() if k!='commands'},indent=2));raise SystemExit(0 if z['all_passed'] else 1)
