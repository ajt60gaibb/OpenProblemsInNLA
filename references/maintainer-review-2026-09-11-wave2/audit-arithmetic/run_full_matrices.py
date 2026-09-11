from pathlib import Path
import subprocess,time,json
out=Path('/private/tmp/nla-review-wave2-artifacts/audit-arithmetic')
package=Path('/private/tmp/nla-review-wave2-artifacts/pr-89/references/colbrook-arithmetic-2026-09-11/submitted/NLA_partial_results_submission_package')
results=[]
for n in range(35,0,-1):
 t=time.monotonic()
 r=subprocess.run([str(out/'build/verify_permanent'),str(package/f'data/ac11/min{n}.txt'),'4'],capture_output=True,text=True)
 item=dict(n=n,returncode=r.returncode,seconds=time.monotonic()-t,stdout=r.stdout,stderr=r.stderr)
 results.append(item)
 print(json.dumps(item),flush=True)
 (out/'runs/full-matrix-checks.json').write_text(json.dumps(results,indent=2))
 if r.returncode: raise SystemExit(r.returncode)
print('ALL 35 FULL MATRIX CHECKS PASS',flush=True)
