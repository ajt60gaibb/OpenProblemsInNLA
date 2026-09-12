import hashlib,json,os,re,subprocess,sys,time
from pathlib import Path

project=Path(sys.argv[1]).resolve();code=sys.argv[2];ref=sys.argv[3];expected=int(sys.argv[4])
ev=project/'reviews'/f'statement-referee-{ref}-root-evidence';ev.mkdir(parents=True,exist_ok=True)
fresh=project/'.verification'/f'root-statement-referee-{ref}';fresh.mkdir(parents=True,exist_ok=True)
assert not (project/'Solution.lean').exists() and not (project/'NLA'/code/'Proof.lean').exists()
files=[f'NLA/{code}/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md','comparator.json','lakefile.toml','lake-manifest.json','lean-toolchain']
def hashes():return {f:hashlib.sha256((project/f).read_bytes()).hexdigest() for f in files}
before=hashes()
lean=subprocess.check_output(['lake','env','which','lean'],cwd=project,text=True).strip()
path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=project,text=True).strip()
old=str((project/'.lake/build/lib/lean').resolve())
parts=[x for x in path.split(':') if str(Path(x).resolve())!=old]
assert len(parts)+1==len(path.split(':'))
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(fresh)]+parts)
records=[]
for name,src in [('definitions',f'NLA/{code}/Definitions.lean'),('challenge','Challenge.lean'),('inspection',str((ev/'Inspect.lean').relative_to(project)))]:
 cmd=[lean]
 if name!='inspection':
  target=fresh/Path(src).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True);cmd+=['-o',str(target)]
 cmd.append(src);start=time.monotonic()
 r=subprocess.run(cmd,cwd=project,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (ev/f'{name}.log').write_bytes(r.stdout)
 rec={'command':cmd,'exit_code':r.returncode,'elapsed_seconds':round(time.monotonic()-start,3),'log':f'{name}.log','sha256':hashlib.sha256(r.stdout).hexdigest()};records.append(rec)
 (ev/'checks.json').write_text(json.dumps({'platform':'local macOS arm64, not Linux Comparator','LEAN_PATH':env['LEAN_PATH'],'commands':records},indent=2)+'\n')
 print(json.dumps(rec),flush=True)
 assert r.returncode==0,r.stdout.decode(errors='replace')
 warnings=r.stdout.count(b'declaration uses `sorry`')
 assert warnings==(expected if name=='challenge' else 0),(name,warnings)
 assert b'error:' not in r.stdout
assert before==hashes()
deps=[]
for pkg in json.loads((project/'lake-manifest.json').read_text())['packages']:
 d=project/'.lake/packages'/pkg['name'];sha=subprocess.check_output(['git','rev-parse','HEAD'],cwd=d,text=True).strip();dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=d,text=True)
 assert sha==pkg['rev'] and not dirty
 deps.append({'package':pkg['name'],'rev':sha,'clean':True})
(ev/'source-identity.json').write_text(json.dumps({'unchanged':True,'files':before,'proof_implementation_absent':True,'dependencies':deps},indent=2)+'\n')
print(json.dumps({'status':'PASS','intentional_challenge_holes':expected,'clean_pinned_packages':len(deps)}),flush=True)
