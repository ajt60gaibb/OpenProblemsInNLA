from pathlib import Path
import json,os,subprocess,sys,hashlib,uuid,datetime,shutil
root=Path(__file__).resolve().parent
lean=Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean')
deps=Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages')
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(root/'out')]+[str(x/'.lake/build/lib/lean') for x in deps.iterdir() if (x/'.lake/build/lib/lean').is_dir()]+[str(lean.parent.parent/'lib/lean')])
modules=sys.argv[1:]
assert modules, 'Pass explicit module names'
runid=datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")+"-"+uuid.uuid4().hex[:8]
runroot=root/"attempts"/runid
runroot.mkdir(parents=True)
records=[]
for i,module in enumerate(modules):
 p=root/'source'/(module.replace('.','/')+'.lean');obj=root/'out'/(module.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 argv=[str(lean),'-R',str(root/'source'),'-o',str(obj),str(p)]
 shutil.copyfile(p, runroot / (module + '.lean'))
 proc=subprocess.run(argv,cwd=root/'source',env=env,capture_output=True,text=True,timeout=300)
 (root/'logs'/(module+'.log')).write_text(proc.stdout+proc.stderr)
 (runroot/(module+'.log')).write_text(proc.stdout+proc.stderr)
 records.append({'module':module,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'argv':argv,'exit_code':proc.returncode,'stdout':proc.stdout,'stderr':proc.stderr})
 print(i+1,module,proc.returncode,flush=True)
 if proc.returncode:
  print(proc.stdout+proc.stderr,flush=True);break
(runroot/'result.json').write_text(json.dumps(records,indent=2)+'\n')
raise SystemExit(0 if len(records)==len(modules) and all(x['exit_code']==0 for x in records) else 1)
