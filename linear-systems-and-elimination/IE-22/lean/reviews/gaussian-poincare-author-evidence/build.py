from pathlib import Path
import os,subprocess,sys,hashlib,json
root=Path(__file__).resolve().parents[2];evidence=Path(__file__).resolve().parent
build=Path('/private/tmp/nla-ie22-gaussian-poincare-author-build');build.mkdir(exist_ok=True)
previous=root.parents[1]/'IE-21/lean'
r=json.loads((previous/'reviews/ie21-final-fidelity-evidence/build-receipt.json').read_text())
for f,d in json.loads((root/'reviews/IE21-DEPENDENCY.json').read_text())['source_sha256'].items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==d
(build/'NLA').mkdir(exist_ok=True)
if not (build/'NLA/IE21').exists():(build/'NLA/IE21').symlink_to(Path(r['build_directory'])/'NLA/IE21',target_is_directory=True)
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean=Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(build),str(root)]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
with (evidence/(sys.argv[1]+'.log')).open('w') as log:
 log.write('IE22 Gaussian foundation author development build; cached pinned dependencies and unchanged verified IE21 cache, no full problem verification claim.\n')
 for f in sys.argv[2:]:
  out=build/Path(f).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(lean),'-o',str(out),f];log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
  p=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log.write(p.stdout+'EXIT '+str(p.returncode)+'\n');log.flush();print(f,p.returncode,p.stdout,flush=True)
  if p.returncode:raise SystemExit(p.returncode)
