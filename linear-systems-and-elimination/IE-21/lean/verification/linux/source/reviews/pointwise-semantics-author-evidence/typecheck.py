#!/usr/bin/env python3
"""Author audit of two exact deterministic semantic bridges; no final verification claim."""
from pathlib import Path
import os, subprocess, tempfile, json, hashlib
root=Path(__file__).resolve().parents[2]
evidence=Path(__file__).resolve().parent
build=Path(tempfile.mkdtemp(prefix='nla-ie21-pointwise-semantics-author-',dir='/private/tmp'))
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean=Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
env=os.environ.copy()
env['LEAN_PATH']=os.pathsep.join([str(build),str(root)]+[str(x/'.lake/build/lib/lean') for x in sorted(packages.iterdir()) if x.is_dir()])
files=['NLA/IE21/Definitions.lean', 'NLA/IE21/MatrixSemantics.lean', 'NLA/IE21/FiniteTrimming.lean', 'NLA/IE21/SphereNet.lean', 'NLA/IE21/QuadraticNet.lean', 'NLA/IE21/PointwiseTrimmingSemantics.lean', 'reviews/pointwise-semantics-author-evidence/SignatureCheck.lean', 'reviews/pointwise-semantics-author-evidence/Axioms.lean']
expected=json.loads((evidence/'input-hashes.json').read_text())['module_source_hashes']
for f,h in expected.items():
 assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h, 'Source changed before review build: '+f
results=[]
with (evidence/'typecheck.log').open('w') as log:
 log.write('Author semantic module audit; not independent or full IE-21 verification.\n')
 log.write('BUILD: '+str(build)+'\n')
 log.write(subprocess.check_output([str(lean),'--version'],text=True))
 for f in files:
  out=build/Path(f).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(lean),'-o',str(out),f]
  log.write('COMMAND: '+' '.join(cmd)+'\n');log.flush()
  r=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log.write(r.stdout+'EXIT: '+str(r.returncode)+'\n');log.flush()
  results.append({'file':f,'exit':r.returncode,'sha256':hashlib.sha256((root/f).read_bytes()).hexdigest()})
  print(f,r.returncode,r.stdout,flush=True)
  if r.returncode:raise SystemExit(r.returncode)
(evidence/'build-receipt.json').write_text(json.dumps({'build':str(build),'files':results},indent=2)+'\n')

for f,h in expected.items():
 assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h, 'Source changed during review build: '+f
