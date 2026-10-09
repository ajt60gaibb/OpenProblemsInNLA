from pathlib import Path
import os,subprocess
root=Path('/private/tmp/tr06-proof-rankone')
packages=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.lake/packages')
lean=Path('/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean')
env=os.environ.copy()
env['LEAN_PATH']=os.pathsep.join(['/private/tmp/tr06-review1/revised-typecheck-build',str(root),'/private/tmp/tr06-leancert/.lake/build/lib/lean']+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
result=subprocess.run([str(lean),'-o',str(root/'NLA/TR06/RankOneCharts.olean'),'NLA/TR06/RankOneCharts.lean'],cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
print(result.stdout,flush=True)
(root/'typecheck.log').write_text(f'exit_code={result.returncode}\n'+result.stdout)
raise SystemExit(result.returncode)
