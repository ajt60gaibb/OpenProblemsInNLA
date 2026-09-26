from pathlib import Path
import os, subprocess, hashlib, json, sys, time
root=Path(__file__).resolve().parent
src=root/'source'
build=root/'build'
logs=root/'logs'
logs.mkdir(exist_ok=True)
lean=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean')
pkgs=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.lake/packages')
paths=[build,Path('/private/tmp/tr06-leancert/.lake/build/lib/lean')]+sorted(p.glob('.lake/build/lib/lean') for p in [])
paths=[build,Path('/private/tmp/tr06-leancert/.lake/build/lib/lean')]+sorted(pkgs.glob('*/.lake/build/lib/lean'))
env=os.environ.copy(); env['LEAN_PATH']=':'.join(map(str,paths))
mods=['Definitions','NormDet','Rectangular','LocalVolume','Density','Radius','Area']
results=[]
for name in mods:
    rel=Path('NLA/TR06')/(name+'.lean'); file=src/rel
    out=build/rel.with_suffix('.olean'); out.parent.mkdir(parents=True,exist_ok=True)
    cmd=[str(lean),'-o',str(out),str(rel)]
    start=time.monotonic(); proc=subprocess.run(cmd,cwd=src,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    log=logs/(name+'.log'); log.write_text(proc.stdout)
    item={'module':'NLA.TR06.'+name,'source_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'exit_code':proc.returncode,'elapsed_seconds':round(time.monotonic()-start,3),'command':cmd,'cwd':str(src),'LEAN_PATH':env['LEAN_PATH']}
    results.append(item); (root/'fresh-rerun.json').write_text(json.dumps(results,indent=2)+'\n')
    print(name,proc.returncode,item['source_sha256'],flush=True)
    if proc.returncode:
        print(proc.stdout,flush=True); sys.exit(proc.returncode)
