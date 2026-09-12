from pathlib import Path
import subprocess,os,json,datetime,time,hashlib
root=Path('/tmp/nla-lean-mi21-worktree/matrix-inequalities-and-norms/MI-21/lean')
e=root/'reviews/proof-referee-2-evidence'; e.mkdir(parents=True,exist_ok=True)
recompiled=e/'recompiled';(recompiled/'NLA/MI21').mkdir(parents=True,exist_ok=True)
lake='/Users/georgestepaniants/.elan/bin/lake'
lean='/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean'
path=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=root,text=True).strip()
env=os.environ.copy();env['LEAN_PATH']=str(recompiled)+':'+path
commands=[('definitions',[lean,'-o',str(recompiled/'NLA/MI21/Definitions.olean'),'NLA/MI21/Definitions.lean']),('proof',[lean,'-o',str(recompiled/'NLA/MI21/Proof.olean'),'NLA/MI21/Proof.lean']),('solution',[lean,'-o',str(recompiled/'Solution.olean'),'Solution.lean'])]
records=[]
for name,cmd in commands:
 t=time.monotonic();start=datetime.datetime.now(datetime.timezone.utc).isoformat()
 p=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (e/(name+'.log')).write_text(p.stdout)
 rec={'name':name,'command':cmd,'started_utc':start,'elapsed_seconds':time.monotonic()-t,'returncode':p.returncode,'log_sha256':hashlib.sha256(p.stdout.encode()).hexdigest(),'log_bytes':len(p.stdout.encode())}
 records.append(rec);(e/'execution.json').write_text(json.dumps({'cwd':str(root),'LEAN_PATH':env['LEAN_PATH'],'commands':records},indent=2)+'\n')
 print(json.dumps(rec),flush=True)
 if p.returncode:
  print(p.stdout[-12000:],flush=True);raise SystemExit(p.returncode)
print('Independent fresh Definitions, Proof, and Solution artifacts all re-elaborated successfully.',flush=True)
