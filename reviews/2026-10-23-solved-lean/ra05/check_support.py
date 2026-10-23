#!/usr/bin/env python3
"""Local source replay of RA05 support, not a full RA05 or Linux proof receipt."""
import argparse,hashlib,json,os,subprocess,tempfile
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument('--lean',required=True,type=Path)
parser.add_argument('--packages',required=True,type=Path)
parser.add_argument('--scaffold',action='store_true')
args=parser.parse_args()
root=Path(__file__).resolve().parent
files=['NLA/Statements/Infrastructure.lean','NLA/Statements/RA05.lean','NLA/Statements/RA06.lean','NLA/Proofs/RA05/HyperplaneDefinitions.lean']
files+=['Challenge.lean'] if args.scaffold else ['NLA/Proofs/RA05/HyperplaneBridge.lean','SupportAudit.lean']
evidence=root/'verification'/('scaffold' if args.scaffold else 'support')
evidence.mkdir(parents=True,exist_ok=True)
result={'scope':'Local macOS exact support source replay only; not full RA05 proof, CI or Comparator acceptance','lean_version':subprocess.check_output([str(args.lean),'--version'],text=True).strip(),'files':[]}
with tempfile.TemporaryDirectory(prefix='nla-ra05-support-') as tmp:
 out=Path(tmp)
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out)]+[str(x/'.lake/build/lib/lean') for x in args.packages.iterdir() if (x/'.lake/build/lib/lean').is_dir()]+[str(args.lean.parent.parent/'lib/lean')])
 for file in files:
  target=out/Path(file).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
  argv=[str(args.lean),'-R',str(root),'-o',str(target),str(root/file)]
  p=subprocess.run(argv,cwd=root,env=env,capture_output=True,text=True,timeout=180)
  (evidence/(file.replace('/','-')+'.log')).write_text(p.stdout+p.stderr)
  result['files'].append({'source':file,'sha256':hashlib.sha256((root/file).read_bytes()).hexdigest(),'argv':argv,'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
  print(file,p.returncode,flush=True)
  if p.returncode:
   print(p.stdout+p.stderr,flush=True)
   break
result['passed']=len(result['files'])==len(files) and all(x['exit_code']==0 for x in result['files'])
(evidence/'result.json').write_text(json.dumps(result,indent=2)+'\n')
raise SystemExit(0 if result['passed'] else 1)
