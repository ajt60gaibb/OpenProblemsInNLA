"""Independent FR-12 statement elaboration into a fresh artifact prefix.
Adapted from this referee's preceding NLA fresh-prefix review drivers.
Writes only the new referee evidence; leaves all frozen statement bytes intact.
"""
from pathlib import Path
import datetime,hashlib,json,os,platform,re,subprocess,tempfile,time

OUT=Path(__file__).resolve().parent
PROJECT=OUT.parent.parent
REPO=PROJECT.parents[2]
BIN=Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')

def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def save(name,value): (OUT/name).write_text(json.dumps(value,indent=2)+'\n')
def capture(argv,cwd=PROJECT):
    p=subprocess.run(argv,cwd=cwd,capture_output=True,text=True,check=True)
    return p.stdout.strip()

frozen=PROJECT/'reviews/statement-freeze.json'
assert sha(frozen)=='5fbbcbce16da324a186dd765d120c883e4800efe2e491fbf069c9f7c74f5372c'
freeze=json.loads(frozen.read_text())
inputs={}
for field,base in [('files',PROJECT),('source_files',REPO)]:
    for name,digest in freeze[field].items():
        path=base/name
        assert sha(path)==digest,name
        inputs[str(path)]={'sha256':digest,'bytes':path.stat().st_size}
save('inputs-before.json',inputs)
assert not (PROJECT/'NLA/FR12/Proof.lean').exists()
assert not (PROJECT/'Solution.lean').exists()
pins=[]
for package in json.loads((PROJECT/'lake-manifest.json').read_text())['packages']:
    folder=PROJECT/'.lake/packages'/package['name']
    rev=capture(['git','rev-parse','HEAD'],folder)
    dirty=capture(['git','status','--porcelain'],folder)
    assert rev==package['rev'] and not dirty,package['name']
    pins.append({'name':package['name'],'expected':package['rev'],'actual':rev,'git_status_porcelain':dirty})
assert len(pins)==10
save('dependencies.json',pins)

(PROJECT/'.verification').mkdir(exist_ok=True)
prefix=Path(tempfile.mkdtemp(prefix='fr12-independent-statement-referee-2-',dir=PROJECT/'.verification'))
old=capture([str(BIN/'lake'),'env','printenv','LEAN_PATH'])
old_target=(PROJECT/'.lake/build/lib/lean').resolve()
parts=[p for p in old.split(os.pathsep) if Path(p).resolve()!=old_target]
assert len(parts)+1==len(old.split(os.pathsep))
env=dict(os.environ)
env['LEAN_PATH']=os.pathsep.join([str(prefix)]+parts)
checks={'reviewer':'/root/leancert_examples','independent_of_author':True,
        'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'platform':platform.platform(),'lean_version':capture([str(BIN/'lean'),'--version']),
        'fresh_prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],
        'old_project_build_excluded':str(old_target),
        'scope':'Fresh macOS statement compilation; pinned dependency artifacts reused; no mathematical proof or Linux Comparator claim',
        'commands':[]}
jobs=[('NLA/FR12/Definitions.lean','definitions',0,True),
      ('Challenge.lean','challenge',7,True),
      ('reviews/statement-referee-2-evidence/Inspect.lean','inspection',0,False)]
for source,label,holes,produce in jobs:
    argv=[str(BIN/'lean')]; artifacts=[]
    if produce:
        for ext,flag in [('.olean','-o'),('.ilean','-i')]:
            target=prefix/Path(source).with_suffix(ext)
            target.parent.mkdir(parents=True,exist_ok=True)
            argv.extend([flag,str(target)]); artifacts.append(target)
    argv.append(source)
    print('Checking',source,flush=True)
    start=time.monotonic()
    p=subprocess.run(argv,cwd=PROJECT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    logfile=OUT/(label+'.log'); logfile.write_bytes(p.stdout)
    checks['commands'].append({'source':source,'source_sha256':sha(PROJECT/source),
        'argv':argv,'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-start,
        'log':logfile.name,'log_sha256':sha(logfile),
        'artifacts':{str(a.relative_to(prefix)):sha(a) for a in artifacts if a.exists()}})
    save('fresh-checks.json',checks)
    print('Exit',p.returncode,flush=True)
    assert p.returncode==0,p.stdout.decode()
    assert p.stdout.count(b'warning:')==holes,p.stdout.decode()
    assert p.stdout.count(b'declaration uses `sorry`')==holes,p.stdout.decode()

axioms=[]
inspection=(OUT/'inspection.log').read_text()
for name,items in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",inspection):
    ax=[a.strip() for a in items.split(',') if a.strip()]
    assert set(ax)<={'propext','Classical.choice','Quot.sound'},(name,ax)
    axioms.append({'declaration':name,'axioms':ax})
for name in re.findall(r"'([^']+)' does not depend on any axioms",inspection):
    axioms.append({'declaration':name,'axioms':[]})
assert len(axioms)==6,len(axioms)
save('definition-axioms.json',{'actual_kernel_checks':6,'reports':axioms})
after={}
for name,info in inputs.items():
    current=sha(name)
    assert current==info['sha256'],name
    after[name]={'before':info['sha256'],'after':current,'unchanged':True}
assert sha(frozen)=='5fbbcbce16da324a186dd765d120c883e4800efe2e491fbf069c9f7c74f5372c'
assert not (PROJECT/'NLA/FR12/Proof.lean').exists() and not (PROJECT/'Solution.lean').exists()
save('inputs-after.json',after)
print(f'PASS: {len(inputs)} frozen inputs unchanged, three fresh modules, seven intentional Challenge holes, six kernel definition audits, ten clean pins',flush=True)
