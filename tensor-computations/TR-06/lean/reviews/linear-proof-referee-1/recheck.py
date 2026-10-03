from pathlib import Path
import hashlib,json,os,subprocess,sys,time
r=Path(__file__).resolve().parent
base=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean')
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(r/'build'),'/private/tmp/tr06-leancert/.lake/build/lib/lean']+[str(p) for p in sorted((base/'.lake/packages').glob('*/.lake/build/lib/lean'))])
mods=sys.argv[1:] or ['NLA/TR06/Definitions','NLA/TR06/AlgebraFiber','NLA/TR06/GraphJacobian']
results=[]
for name in mods:
 p=r/'source'/(name+'.lean');out=r/'build'/(name+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
 cmd=[str(base/'.tools/lean-4.33.1-darwin_aarch64/bin/lean'),'-o',str(out),name+'.lean'];t=time.monotonic()
 a=subprocess.run(cmd,cwd=r/'source',env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 log=r/'logs'/(p.stem+'.log');log.write_text(a.stdout)
 record={'module':name,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'command':cmd,'LEAN_PATH':env['LEAN_PATH'],'exit_code':a.returncode,'seconds':time.monotonic()-t}
 results.append(record);(r/(p.stem+'-receipt.json')).write_text(json.dumps(record,indent=2)+'\n')
 print(name,'exit',a.returncode,record['source_sha256'],flush=True);print(a.stdout,flush=True)
 if a.returncode:sys.exit(a.returncode)
