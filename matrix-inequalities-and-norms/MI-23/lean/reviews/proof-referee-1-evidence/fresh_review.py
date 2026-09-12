"""Independent MI-23 final review: fresh project source and proof-term inspection.
Adapts the reviewer’s earlier separate-prefix drivers. This is a local check,
not actual Linux Comparator/default-kernel replay or a full library rebuild.
"""
from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, tempfile, time
OUT=Path(__file__).resolve().parent
PROJECT=OUT.parents[1]
REPO=PROJECT.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,data):(OUT/name).write_text(json.dumps(data,indent=2)+'\n')
def capture(args,cwd=PROJECT):return subprocess.check_output(args,cwd=cwd).decode().strip()
freeze_path=PROJECT/'reviews/proof-freeze.json'
assert sha(freeze_path)=='18fbf9a74e6006ca2b4159be62730c6df4faf38d472250b8ca1e7e54bf392ecb'
freeze=json.loads(freeze_path.read_text());assert len(freeze['files'])==25
inputs={}
for rel,rec in freeze['files'].items():
    path=PROJECT/rel
    assert sha(path)==rec['sha256'] and path.stat().st_size==rec['bytes'],rel
    inputs[rel]=rec
save('inputs-before.json',inputs)
sources={}
for rel in ['matrix-inequalities-and-norms/MI-23/README.md','matrix-inequalities-and-norms/MI-23/solution.tex','matrix-inequalities-and-norms/MI-23/solution.md','matrix-inequalities-and-norms/MI-23/solution.pdf']:
    b=subprocess.check_output(['git','show',freeze['repository_base']+':'+rel],cwd=REPO)
    assert (REPO/rel).read_bytes()==b,rel
    sources[rel]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'matches_immutable_base':True}
save('original-sources.json',sources)
manifest=json.loads((PROJECT/'lake-manifest.json').read_text());pins=[]
for pkg in manifest['packages']:
    folder=PROJECT/'.lake/packages'/pkg['name']
    head=capture(['git','rev-parse','HEAD'],folder)
    status=capture(['git','status','--porcelain'],folder)
    assert head==pkg['rev'] and not status,pkg['name']
    pins.append({'name':pkg['name'],'revision':head,'status':status})
assert len(pins)==10;save('dependencies.json',pins)
parent=Path('/tmp/nla-lean-formalization/independent-prefixes');parent.mkdir(parents=True,exist_ok=True)
prefix=Path(tempfile.mkdtemp(prefix='mi23-final-referee1-',dir=parent))
old=(PROJECT/'.lake/build/lib/lean').resolve()
paths=capture(['lake','env','printenv','LEAN_PATH']).split(os.pathsep)
env=dict(os.environ)
env['LEAN_PATH']=os.pathsep.join([str(prefix)]+[q for q in paths if q and Path(q).resolve()!=old])
checks={'scope':'Independent local macOS fresh target elaboration; exact clean pinned dependency caches reused; no Linux verification claim.','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'platform':platform.platform(),'lean_version':capture(['lean','--version']),'source_commit':freeze['repository_base'],'fresh_prefix':str(prefix),'project_cache_excluded':str(old),'LEAN_PATH':env['LEAN_PATH'],'commands':[]}
modules=['NLA/MI23/Definitions','NLA/MI23/FunctionalCalculus','NLA/MI23/SpectralNorm','NLA/MI23/NormBounds','NLA/MI23/Witness','NLA/MI23/Arithmetic','NLA/MI23/Proof','Solution','Challenge']
for mod in modules+['reviews/proof-referee-1-evidence/Inspect']:
    src=PROJECT/(mod+'.lean');cmd=['lean'];artifacts=[]
    if mod in modules:
        for flag,suffix in [('-o','.olean'),('-i','.ilean')]:
            dest=prefix/(mod+suffix);dest.parent.mkdir(parents=True,exist_ok=True)
            cmd += [flag,str(dest)];artifacts.append(dest)
    cmd.append(str(src));name='inspection.log' if mod not in modules else mod.replace('/','-')+'.log'
    print('Checking '+mod,flush=True)
    start=time.monotonic();proc=subprocess.run(cmd,cwd=PROJECT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (OUT/name).write_bytes(proc.stdout)
    checks['commands'].append({'source':str(src.relative_to(PROJECT)),'source_sha256':sha(src),'command':cmd,'exit_code':proc.returncode,'seconds':time.monotonic()-start,'log':name,'log_sha256':sha(OUT/name),'artifacts':{str(q.relative_to(prefix)):sha(q) for q in artifacts if q.exists()}})
    save('fresh-checks.json',checks)
    print(f'Exit {proc.returncode}: {name}',flush=True)
    if proc.returncode:print(proc.stdout.decode());raise SystemExit(proc.returncode)
for rel,rec in inputs.items():assert sha(PROJECT/rel)==rec['sha256'],rel
save('inputs-after.json',{rel:{'sha256':sha(PROJECT/rel),'unchanged':True} for rel in inputs})
text=(OUT/'Solution.log').read_text()
axioms=re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]",text)
assert len(axioms)==64 and len({n for n,_ in axioms})==64
for n,axs in axioms:assert set(x.strip() for x in axs.split(','))=={'propext','Classical.choice','Quot.sound'},n
assert len(re.findall(r'declaration uses `sorry`',(OUT/'Challenge.log').read_text()))==8
for c in checks['commands']:
    if c['source']!='Challenge.lean':assert not re.search(r'\b(?:error|warning):',(OUT/c['log']).read_text()),c['source']
save('axiom-audit.json',{'declaration_count':64,'declarations':{n:[x.strip() for x in axs.split(',')] for n,axs in axioms},'verdict':'PASS'})
checks['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();checks['verdict']='PASS';save('fresh-checks.json',checks)
print('PASS: all frozen target sources freshly elaborate; 64 standard-three/kernel reports; independent semantic/certificate inspection accepted.',flush=True)
