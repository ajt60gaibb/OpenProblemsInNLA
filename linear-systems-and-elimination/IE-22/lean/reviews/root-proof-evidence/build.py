from pathlib import Path
import os, subprocess, sys, hashlib, json
project=Path(__file__).resolve().parents[2]
review=Path(__file__).resolve().parent
build=Path('/private/tmp/nla-ie22-root-proof-build')
build.mkdir(exist_ok=True)
for f,h in json.loads((project/'reviews/IE21-DEPENDENCY.json').read_text())['source_sha256'].items():
    assert hashlib.sha256((project/f).read_bytes()).hexdigest()==h, f
for f,h in json.loads((project/'reviews/statement-freeze.json').read_text())['mathematical_boundary_sha256'].items():
    assert hashlib.sha256((project/f).read_bytes()).hexdigest()==h, f
(build/'NLA').mkdir(exist_ok=True)
if not (build/'NLA/IE21').exists():
    (build/'NLA/IE21').symlink_to('/private/tmp/nla-ie21-complete-author-pg78c47s/NLA/IE21',target_is_directory=True)
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean='/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean'
env=dict(os.environ)
env['LEAN_PATH']=os.pathsep.join([str(build),str(project)]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
with (review/(sys.argv[1]+'.log')).open('w') as log:
    log.write('Local cached development check only; frozen statements and all 31 vendored IE21 sources byte-checked. No Linux verification claim.\n')
    for f in sys.argv[2:]:
        out=build/Path(f).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
        cmd=[lean,'-o',str(out),f]
        log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
        result=subprocess.run(cmd,cwd=project,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log.write(result.stdout+'EXIT '+str(result.returncode)+'\n');log.flush()
        print(f,result.returncode,result.stdout,flush=True)
        if result.returncode:raise SystemExit(result.returncode)
