from pathlib import Path
import os,subprocess,sys
project=Path('/Users/ajt253/Documents/OpenProblemsInNLA/linear-systems-and-elimination/IE-06/lean')
lean=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean')
cache=Path('/Users/ajt253/Documents/ChrisResearch/RRF/SIMAX Version/Revision 2.2/lean/.lake/packages')
out=Path('/private/tmp/ie06-frobenius-build');out.mkdir(exist_ok=True)
paths=[str(p/'.lake/build/lib/lean') for p in cache.iterdir() if (p/'.lake/build/lib/lean').is_dir()]
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(out)]+paths+[str(lean.parent.parent/'lib/lean')]);env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
mods=['Definitions','GaussianNull','GaussianQuadratic','GaussianFrobenius','GaussianSmallest']
for name in mods:
 src=project/f'NLA/IE06/{name}.lean';dst=out/f'NLA/IE06/{name}.olean';dst.parent.mkdir(parents=True,exist_ok=True)
 if name!='GaussianSmallest' and dst.exists() and dst.stat().st_mtime>src.stat().st_mtime: continue
 cp=subprocess.run([str(lean),'-o',str(dst),str(src.relative_to(project))],cwd=project,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 Path(f'/private/tmp/ie06-{name}.log').write_text(cp.stdout)
 print(cp.stdout,flush=True)
 if cp.returncode: raise SystemExit(cp.returncode)
