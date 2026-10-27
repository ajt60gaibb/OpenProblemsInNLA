#!/usr/bin/env python3
"""Rebuild this author evidence source closure with no borrowed project objects.
Supply an official Lean 4.33.1 binary and the exact pinned package checkout root.
This is an author replay, not independent review or CI/Comparator evidence.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,subprocess,sys,tempfile
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--lean',required=True,type=Path)
p.add_argument('--packages',required=True,type=Path)
p.add_argument('--output',type=Path)
a=p.parse_args();root=Path(__file__).resolve().parent
receipt=json.loads((root/'AUTHOR_KERNEL_RECEIPT.json').read_text())
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
for q in receipt['modules']:
 source=root/'sources'/Path(q['module'].replace('.','/')+'.lean')
 if sha(source)!=q['sha256']:raise SystemExit('Source hash mismatch: '+q['module'])
version=subprocess.check_output([str(a.lean),'--version'],text=True).strip()
if 'version 4.33.1,' not in version or '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' not in version:
 raise SystemExit('Unexpected official compiler version: '+version)
for q in receipt['dependency_pins']:
 actual=subprocess.check_output(['git','-C',str(a.packages/q['name']),'rev-parse','HEAD'],text=True).strip()
 if actual!=q['expected']:raise SystemExit('Dependency pin mismatch: '+q['name'])
out=a.output or Path(tempfile.mkdtemp(prefix='re06-rangefinder-author-replay-'))
if a.output:out.mkdir(parents=True,exist_ok=False)
(out/'objects').mkdir();(out/'logs').mkdir()
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out/'objects')]+[str(q/'.lake/build/lib/lean') for q in sorted(a.packages.iterdir()) if (q/'.lake/build/lib/lean').is_dir()]+[str(a.lean.parent.parent/'lib/lean')])
records=[]
for q in receipt['modules']:
 m=q['module'];rel=Path(m.replace('.','/')+'.lean');obj=out/'objects'/rel.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 argv=[str(a.lean),'-R',str(root/'sources'),'-o',str(obj),str(root/'sources'/rel)]
 proc=subprocess.run(argv,cwd=root/'sources',env=env,capture_output=True,text=True,timeout=300)
 (out/'logs'/(m+'.log')).write_text(proc.stdout+proc.stderr)
 records.append(dict(module=m,sha256=q['sha256'],argv=argv,exit_code=proc.returncode,stdout=proc.stdout,stderr=proc.stderr))
 (out/'RESULT.json').write_text(json.dumps(dict(role='Author source-only replay',timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),compiler_version=version,records=records),indent=2)+'\n')
 print(m,proc.returncode,flush=True)
 if proc.returncode:raise SystemExit(proc.returncode)
controls=[]
for q in receipt.get('negative_controls',[]):
 argv=[str(a.lean),'-R',str(root/'controls'),str(root/'controls'/q['file'])]
 proc=subprocess.run(argv,cwd=root/'controls',env=env,capture_output=True,text=True,timeout=300)
 controls.append(dict(file=q['file'],argv=argv,exit_code=proc.returncode,stdout=proc.stdout,stderr=proc.stderr))
 (out/'NEGATIVE_CONTROL_RESULTS.json').write_text(json.dumps(controls,indent=2)+'\n')
 if proc.returncode==0 or q['expected_diagnostic'] not in proc.stdout+proc.stderr:
  raise SystemExit('Negative declaration-kind control did not reject as expected')
print('Accepted',len(records),'source outcomes and rejected',len(controls),'negative controls; output',out)
