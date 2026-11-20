from pathlib import Path
import os,sys,subprocess,json,hashlib,datetime
root=Path(__file__).resolve().parent
packages=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.lake/packages')
env=os.environ.copy()
env['LEAN_PATH']=os.pathsep.join([str(root),'/private/tmp/tr06-leancert/.lake/build/lib/lean']+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
source=Path(sys.argv[1]);cmd=['/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean','-o',str(root/source.with_suffix('.olean')),str(source)]
r=subprocess.run(cmd,cwd=root,env=env,text=True,capture_output=True)
(root/(source.stem+'.log')).write_text(r.stdout+r.stderr)
(root/(source.stem+'-receipt.json')).write_text(json.dumps({'source':str(source),'sha256':hashlib.sha256((root/source).read_bytes()).hexdigest(),'command':cmd,'exit_code':r.returncode,'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n')
print(r.stdout+r.stderr);sys.exit(r.returncode)
