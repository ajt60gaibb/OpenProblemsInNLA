"""Compile IE23 proof-development modules with read-only pinned MI22 dependencies.
This driver never invokes Lake or mutates/copies the dependency cache. The
final freeze will use a separate fresh prefix for every project module.
"""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time
P=Path(__file__).resolve().parents[1]
D=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
B=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
PREFIX=P/'.verification/ie23-proof-development'
PREFIX.mkdir(parents=True,exist_ok=True)
packages=json.loads((P/'lake-manifest.json').read_text())['packages']
env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(PREFIX)]+
 [str(D/x['name']/'.lake/build/lib/lean') for x in reversed(packages)]+[str(B.parent/'lib/lean')]))
for name in sys.argv[1:]:
    rel=Path(name if name.endswith('.lean') else name.replace('.','/')+'.lean')
    dst=PREFIX/rel.with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
    args=[str(B/'lean'),'-o',str(dst),str(rel)]
    print('Checking',rel,flush=True)
    cp=subprocess.run(args,cwd=P,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    label=str(rel).replace('/','-').removesuffix('.lean')
    log=P/'verification'/('development-'+label+'.log');log.write_bytes(cp.stdout)
    print(cp.stdout.decode(),end='',flush=True)
    if cp.returncode:sys.exit(cp.returncode)
