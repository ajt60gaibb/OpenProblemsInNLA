from pathlib import Path
import os,subprocess,json,hashlib,time
r=Path(__file__).resolve().parent
base=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean')
lean=base/'.tools/lean-4.33.1-darwin_aarch64/bin/lean'
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(r/'build'),'/private/tmp/tr06-leancert/.lake/build/lib/lean']+[str(p) for p in sorted((base/'.lake/packages').glob('*/.lake/build/lib/lean'))])
rec=[]
for f in json.loads((r/'SOURCE-SNAPSHOT.json').read_text())['order']:
 out=r/'build'/Path(f).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 cmd=[str(lean),'-o',str(out),f];t=time.monotonic();x=subprocess.run(cmd,cwd=r,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=r/'logs'/(Path(f).stem+'.log');log.parent.mkdir(exist_ok=True);log.write_text(x.stdout)
 rec.append({'file':f,'command':cmd,'exit':x.returncode,'source_sha256':hashlib.sha256((r/f).read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'seconds':time.monotonic()-t})
 (r/'RERUN.json').write_text(json.dumps({'LEAN_PATH':env['LEAN_PATH'],'runs':rec},indent=2)+'\n')
 print(f,'EXIT',x.returncode,flush=True);print(x.stdout,flush=True)
 if x.returncode:raise SystemExit(x.returncode)
