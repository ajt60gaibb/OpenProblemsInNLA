from pathlib import Path
import os,subprocess,sys,hashlib,json
receipt_dir=Path(__file__).resolve().parent
project=Path('/Users/ajt253/Documents/OpenProblemsInNLA/linear-systems-and-elimination/IE-06/lean')
lean=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean')
cache=Path('/Users/ajt253/Documents/ChrisResearch/RRF/SIMAX Version/Revision 2.2/lean/.lake/packages')
out=Path('/private/tmp/ie06-frobenius-build');out.mkdir(exist_ok=True)
paths=[str(p/'.lake/build/lib/lean') for p in cache.iterdir() if (p/'.lake/build/lib/lean').is_dir()]
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(out)]+paths+[str(lean.parent.parent/'lib/lean')]);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
mods=['Definitions','GaussianNull','GaussianQuadratic','GaussianFrobenius','GaussianSmallest','GaussianRegression','GaussianDeterminantMoments']
sources={name:hashlib.sha256((project/f'NLA/IE06/{name}.lean').read_bytes()).hexdigest() for name in mods}
logs=[]
for name in mods:
 src=project/f'NLA/IE06/{name}.lean';dst=out/f'NLA/IE06/{name}.olean';dst.parent.mkdir(parents=True,exist_ok=True)
 cp=subprocess.run([str(lean),'-o',str(dst),str(src.relative_to(project))],cwd=project,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 Path(f'/private/tmp/ie06-{name}.log').write_text(cp.stdout)
 logs.append(name+"\n"+cp.stdout)
 print(cp.stdout,flush=True)
 if cp.returncode: raise SystemExit(cp.returncode)

after={name:hashlib.sha256((project/f'NLA/IE06/{name}.lean').read_bytes()).hexdigest() for name in mods}
if sources != after: raise SystemExit('source changed during compilation')
(receipt_dir/'compile.log').write_text('\n'.join(logs))
(receipt_dir/'receipt.json').write_text(json.dumps({'scope':'Direct local macOS kernel compilation with before/after source hashes; not Linux sandbox or full Comparator','compiler':str(lean),'sources_sha256':sources,'exit_code':0,'log_sha256':hashlib.sha256((receipt_dir/'compile.log').read_bytes()).hexdigest()},indent=2)+'\n')
