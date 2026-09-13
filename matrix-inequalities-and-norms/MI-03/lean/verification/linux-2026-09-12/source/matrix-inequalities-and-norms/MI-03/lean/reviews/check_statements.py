"""Author statement elaboration; no proof is implemented by these checks."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time,tempfile

p=Path(__file__).resolve().parent.parent
ev=p/'reviews';(p/'.verification').mkdir(exist_ok=True)
fresh=Path(tempfile.mkdtemp(prefix='author-statements-',dir=p/'.verification'))
assert not (p/'Solution.lean').exists() and not (p/'NLA/MI03/Proof.lean').exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
lean=subprocess.check_output(['lake','env','which','lean'],cwd=p,text=True).strip()
oldpath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=p,text=True).strip().split(':')
old=str((p/'.lake/build/lib/lean').resolve())
paths=[x for x in oldpath if str(Path(x).resolve())!=old]
assert len(paths)+1==len(oldpath)
env=dict(os.environ,LEAN_PATH=':'.join([str(fresh)]+paths))
commands=[]
for name,rel in [('definitions','NLA/MI03/Definitions.lean'),('challenge','Challenge.lean'),('inspection','reviews/InspectStatements.lean')]:
 cmd=[lean]
 if name!='inspection':
  out=fresh/Path(rel).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);cmd+=['-o',str(out)]
 cmd+=[rel];start=time.monotonic()
 cp=subprocess.run(cmd,cwd=p,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=ev/f'fresh-{name}.log';log.write_bytes(cp.stdout)
 rec=dict(command=cmd,exit_code=cp.returncode,elapsed_seconds=round(time.monotonic()-start,3),log=log.name,sha256=sha(cp.stdout))
 commands.append(rec);print(json.dumps(rec),flush=True)
 (ev/'fresh-checks.json').write_text(json.dumps(dict(platform='Local macOS arm64, author checks only; not Linux Comparator',LEAN_PATH=env['LEAN_PATH'],commands=commands),indent=2)+'\n')
 assert cp.returncode==0,cp.stdout.decode()
 assert cp.stdout.count(b'declaration uses `sorry`')==(8 if name=='challenge' else 0)
 assert b'error:' not in cp.stdout
pins=[]
for package in json.loads((p/'lake-manifest.json').read_text())['packages']:
 d=p/'.lake/packages'/package['name']
 rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=d,text=True).strip()
 dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=d,text=True)
 assert rev==package['rev'] and not dirty
 pins.append(dict(name=package['name'],rev=rev,tracked_source_clean=True))
(ev/'dependency-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
log=(ev/'fresh-inspection.log').read_text()
axioms=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
assert len(axioms)==20
for n,raw in axioms:assert set(x.strip() for x in raw.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},n
for term in ['ContinuousLinearMap.hasOpNorm','EuclideanSpace','CFC.sqrt','Matrix.PosSemidef','sInf','Complex.exp']:
 assert term in log,term
(ev/'definition-axioms.json').write_text(json.dumps(dict(count=20,axioms=axioms,all_standard_three_only=True,proof_absent=True),indent=2)+'\n')
print(json.dumps(dict(status='PASS',fresh_commands=3,definition_audits=20,pins=len(pins),intentional_Challenge_holes=8)),flush=True)
