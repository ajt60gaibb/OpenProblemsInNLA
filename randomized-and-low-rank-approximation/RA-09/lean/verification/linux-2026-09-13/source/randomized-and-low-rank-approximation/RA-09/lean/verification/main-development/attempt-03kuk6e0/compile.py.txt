"""RA-09 main development direct-source compiler, with exact pinned dependencies.

One initially empty evolving project prefix; read-only MI22 dependency objects.
Retains every attempted source/log. No Lake, copying or dependency build.
Adapted from the campaign statement and MF16 development runners.
"""
from pathlib import Path
import datetime, hashlib, json, os, platform, subprocess, sys, tempfile, time

E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
L=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
f=json.loads((P/'reviews/statement-freeze.json').read_text())
for n,h in f['files'].items():assert sha(P/n)==h,n
assert sha(P/'NLA/RA09/Frobenius.lean')=='f2d038d3d2f5195074ab5acc973771aaf57782d9ce9271c6fbc7132f8178c6ad'
config=E/'environment.json'
if not config.exists():
    pins=[]
    for d in json.loads((P/'lake-manifest.json').read_text())['packages']:
        path=C/d['name'];actual=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
        assert actual==d['rev'] and not subprocess.check_output(['git','-C',str(path),'status','--porcelain=v1'])
        pins.append({'name':d['name'],'rev':actual,'path':str(path)})
    prefix=Path(tempfile.mkdtemp(prefix='ra09-main-',dir='/tmp/nla-lean-formalization/independent-prefixes'))
    assert not list(prefix.iterdir())
    packages=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib','leancert']
    paths=[prefix,*[C/n/'.lake/build/lib/lean' for n in packages],L/'lib/lean']
    environment={'prefix':str(prefix),'LEAN_PATH':':'.join(map(str,paths)),'pins':pins,
        'toolchain':subprocess.check_output([str(L/'bin/lean'),'--version'],text=True).strip(),
        'platform':platform.platform(),'initial_project_prefix_empty':True,'scope':'Main development, not independent final proof review or Linux; no prior target objects.'}
    config.write_text(json.dumps(environment,indent=2)+'\n')
environment=json.loads(config.read_text());prefix=Path(environment['prefix'])
env=os.environ.copy();env['LEAN_PATH']=environment['LEAN_PATH'];env['PYTHONDONTWRITEBYTECODE']='1'
attempt=Path(tempfile.mkdtemp(prefix='attempt-',dir=E))
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'environment_sha256':sha(config),
        'runner_sha256':sha(Path(__file__)),'commands':[]}
(attempt/'compile.py.txt').write_bytes(Path(__file__).read_bytes())
assert len(sys.argv)>1
for rel in sys.argv[1:]:
    source=P/rel;assert source.is_file() and source.resolve().is_relative_to(P.resolve())
    (attempt/(rel.replace('/','-')+'.txt')).write_bytes(source.read_bytes())
    target=prefix/Path(rel).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
    cmd=[str(L/'bin/lean'),'-o',str(target),'-i',str(target.with_suffix('.ilean')),str(source)]
    start=time.monotonic();result=subprocess.run(cmd,cwd=P,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=240)
    log=attempt/(rel.replace('/','-').replace('.lean','.log'));log.write_bytes(result.stdout)
    row={'source':rel,'source_sha256':sha(source),'command':cmd,'exit_code':result.returncode,
         'seconds':time.monotonic()-start,'log':log.name,'log_sha256':sha(log)}
    record['commands'].append(row);(attempt/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    print(rel,result.returncode,round(row['seconds'],2),flush=True)
    if result.returncode:
        print(log.read_text()[:16000],flush=True)
        (E/'latest.json').write_text(json.dumps({'attempt':str(attempt),'verdict':'FAILED retained development attempt'},indent=2)+'\n')
        raise SystemExit(result.returncode)
for n,h in f['files'].items():assert sha(P/n)==h,n
record['verdict']='PASS direct development source compilation'
(attempt/'result.json').write_text(json.dumps(record,indent=2)+'\n')
(E/'latest.json').write_text(json.dumps({'attempt':str(attempt),'verdict':record['verdict']},indent=2)+'\n')
print('PASS',attempt,flush=True)
