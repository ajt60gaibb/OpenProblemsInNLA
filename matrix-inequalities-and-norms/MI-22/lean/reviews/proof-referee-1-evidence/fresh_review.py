"""Independent MI-22 final referee 1. Fresh project objects; clean pinned
Mathlib/LeanCert dependency caches reused. Local macOS only, not Linux Comparator.
Adapted from this reviewer's earlier final-review drivers; no author checker used.
"""
from pathlib import Path
import datetime, hashlib, json, os, platform, re, subprocess, tempfile, time
OUT=Path(__file__).resolve().parent
PROJECT=OUT.parents[1]
REPO=PROJECT.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,x):(OUT/name).write_text(json.dumps(x,indent=2)+'\n')
def capture(args,cwd=PROJECT):return subprocess.check_output(args,cwd=cwd).decode().strip()
fp=PROJECT/'verification/proof-freeze.json'
assert sha(fp)=='f1c267a6aa600074d3b054863926d5f9cdbf6b0eadb83912a912277ac54018a0'
assert sha(PROJECT/'reviews/proof-completion.md')=='f664009cb8df3231252be68c3f944c9ccd5ff69c2601d2d3e85895722cbcde7b'
f=json.loads(fp.read_text());assert len(f['files'])==104 and len(f['source_files'])==8
for rel,r in f['files'].items():
    q=PROJECT/rel
    assert sha(q)==r['sha256'] and q.stat().st_size==r['bytes'],rel
save('inputs-before.json',f['files'])
sf=PROJECT/'reviews/statement-freeze.json'
assert sha(sf)=='d83d2a2baa1788f6e5ec284c70bb12d7618f4963a9426777a37b2af4135ed756'
s=json.loads(sf.read_text());assert len(s['files'])==27
reg=json.loads((PROJECT/'verification/build-registration.json').read_text())
archive=PROJECT/reg['original_archive']
assert sha(archive)==reg['old_sha256']==s['files']['lakefile.toml']
assert (PROJECT/'lakefile.toml').read_bytes()==archive.read_bytes()+reg['exact_append'].encode()
assert sha(PROJECT/'lakefile.toml')==reg['new_sha256']
for rel,h in s['files'].items():
    if rel!='lakefile.toml':assert sha(PROJECT/rel)==h,rel
save('statement-integrity.json',{'frozen_files':27,'unchanged_files':26,'only_exception':reg,'original_statement_freeze':sha(sf)})
sources={}
for rel,h in f['source_files'].items():
    b=subprocess.check_output(['git','show',f['source_commit']+':'+rel],cwd=REPO)
    assert (REPO/rel).read_bytes()==b and sha(REPO/rel)==h,rel
    sources[rel]={'sha256':h,'bytes':len(b),'matches_immutable_git_blob':True}
save('original-sources.json',sources)
pins=[]
for pkg in json.loads((PROJECT/'lake-manifest.json').read_text())['packages']:
    folder=PROJECT/'.lake/packages'/pkg['name'];head=capture(['git','rev-parse','HEAD'],folder)
    status=capture(['git','status','--porcelain'],folder)
    assert head==pkg['rev'] and not status,pkg['name']
    pins.append({'name':pkg['name'],'revision':head,'status':status})
assert len(pins)==10;save('dependencies.json',pins)
parent=Path('/tmp/nla-lean-formalization/independent-prefixes');parent.mkdir(parents=True,exist_ok=True)
prefix=Path(tempfile.mkdtemp(prefix='mi22-final-referee1-',dir=parent))
old=(PROJECT/'.lake/build/lib/lean').resolve()
paths=capture(['lake','env','printenv','LEAN_PATH']).split(os.pathsep)
def resolved(q):return (PROJECT/q).resolve()
filtered=[q for q in paths if q and resolved(q)!=old]
assert all(resolved(q)!=old for q in filtered)
env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join([str(prefix)]+filtered)
checks={'scope':'Independent local macOS elaboration of all project source; ten exact clean pinned dependency caches reused. No Linux Comparator/default-kernel or library-rebuild claim.',
'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'platform':platform.platform(),'lean_version':capture(['lean','--version']),
'source_commit':f['source_commit'],'fresh_prefix':str(prefix),'project_cache_excluded':str(old),'LEAN_PATH':env['LEAN_PATH'],'commands':[]}
mods=['NLA/MI22/Definitions','NLA/MI22/FunctionalCalculus','NLA/MI22/Norms','NLA/MI22/SingularValues','NLA/MI22/Witness','NLA/MI22/ExactData','NLA/MI22/Proof','Solution','Challenge']
for mod in mods+['reviews/proof-referee-1-evidence/Inspect']:
    src=PROJECT/(mod+'.lean');cmd=['lean'];artifacts=[]
    if mod in mods:
        for flag,suffix in [('-o','.olean'),('-i','.ilean')]:
            d=prefix/(mod+suffix);d.parent.mkdir(parents=True,exist_ok=True)
            cmd += [flag,str(d)];artifacts.append(d)
    cmd.append(str(src));name='inspection.log' if mod not in mods else mod.replace('/','-')+'.log'
    print('Checking '+mod,flush=True);start=time.monotonic()
    proc=subprocess.run(cmd,cwd=PROJECT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (OUT/name).write_bytes(proc.stdout)
    checks['commands'].append({'source':str(src.relative_to(PROJECT)),'source_sha256':sha(src),'command':cmd,'exit_code':proc.returncode,'seconds':time.monotonic()-start,'log':name,'log_sha256':sha(OUT/name),'artifacts':{str(q.relative_to(prefix)):sha(q) for q in artifacts if q.exists()}})
    save('fresh-checks.json',checks);print('Exit '+str(proc.returncode)+': '+name,flush=True)
    if proc.returncode:print(proc.stdout.decode());raise SystemExit(proc.returncode)
for rel,r in f['files'].items():assert sha(PROJECT/rel)==r['sha256'],rel
save('inputs-after.json',{rel:{'sha256':sha(PROJECT/rel),'unchanged':True} for rel in f['files']})
allowed={'propext','Classical.choice','Quot.sound'};reports={}
for name,count in [('NLA-MI22-Proof.log',9),('Solution.log',8),('inspection.log',8)]:
    axs=re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]",(OUT/name).read_text())
    assert len(axs)==count,(name,len(axs))
    for n,a in axs:
        deps=set(x.strip() for x in a.split(','));assert deps<=allowed,n
        reports[n]=sorted(deps)
assert len(reports)==17
assert len(re.findall(r'declaration uses `sorry`',(OUT/'Challenge.log').read_text()))==8
for c in checks['commands']:
    if c['source']!='Challenge.lean':assert not re.search(r'\b(?:error|warning):',(OUT/c['log']).read_text()),c['source']
save('axiom-audit.json',{'distinct_declarations':17,'reports':25,'allowed':sorted(allowed),'declarations':reports,'verdict':'PASS'})
checks['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();checks['verdict']='PASS';save('fresh-checks.json',checks)
print('PASS: ten fresh elaborations, 17 distinct standard-three declarations, 8 exports, all frozen bytes preserved.',flush=True)
