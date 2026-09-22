from pathlib import Path
import argparse,datetime,hashlib,json,os,subprocess,sys,time
p=argparse.ArgumentParser();p.add_argument('--attempt',type=int,default=1);a=p.parse_args()
assert a.attempt>=1
base=Path(__file__).resolve().parent;repo=base/'repo'
receipt=json.loads((base/'input-receipt.json').read_text())
preparation=json.loads((base/'preparation.json').read_text())
assert os.getuid()==1000 and preparation['input_sha256']==receipt['input_sha256']
assert subprocess.check_output(['git','status','--porcelain'],cwd=repo,text=True)==''
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==preparation['guest_repository_commit']
assert len(receipt['theorem_names'])==23
log=base/f'verification-driver-attempt-{a.attempt}.log'
record_path=base/f'runner-result-attempt-{a.attempt}.json'
assert not log.exists() and not record_path.exists()
env=os.environ.copy()
env.update({'PATH':'/home/admin/.elan/bin:/home/admin/mf21-tools/go/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin','XDG_RUNTIME_DIR':'/run/user/1000','DBUS_SESSION_BUS_ADDRESS':'unix:path=/run/user/1000/bus'})
env.pop('NLA_LEAN_SKIP_CACHE',None)
command=['/home/admin/mf21-harness/tools/lean/verify.sh',receipt['project_path'],'/home/admin/nla-lean-tools']
old_logs={str(p) for p in Path('/home/admin/nla-lean-tools/logs').glob('verify-*')}
record={'scope':'Complete original IE-21 target and every frozen required declaration','selected_theorem_count':len(receipt['theorem_names']),'operator_role':'Mechanical verifier operator; authored separate Gaussian/spherical modules; not an independent final referee','publication_commit':receipt['publication_commit'],'guest_repository_commit':preparation['guest_repository_commit'],'command':command,'cwd':str(repo),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'running','dependency_observer':'Separate read-only capture of fresh manifest/Git heads/source bytes; no controls or proof behavior changed.'}
record_path.write_text(json.dumps(record,indent=2)+'\n')
capture_log=base/f'dependency-capture-attempt-{a.attempt}.log';capture_attempts=0
with log.open('w') as stream,capture_log.open('w') as capture_stream:
 child=subprocess.Popen(command,cwd=repo,env=env,stdout=stream,stderr=subprocess.STDOUT)
 while child.poll() is None:
  if not (base/'dependency-evidence/dependency-receipt.json').exists():
   capture_attempts+=1
   capture=subprocess.run(['/usr/bin/python3',str(base/'capture-dependency-receipt.py')],env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
   if capture.returncode!=5:
    capture_stream.write('CAPTURE '+str(capture_attempts)+' EXIT '+str(capture.returncode)+'\n'+capture.stdout);capture_stream.flush()
  time.sleep(1)
 code=child.wait()
new_logs=sorted({str(p) for p in Path('/home/admin/nla-lean-tools/logs').glob('verify-*')}-old_logs)
record.update({'status':'finished','exit_code':code,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verification_log_directories':new_logs,'dependency_capture_attempts':capture_attempts,'dependency_capture_succeeded':(base/'dependency-evidence/dependency-receipt.json').exists()})
record_path.write_text(json.dumps(record,indent=2)+'\n')
sys.exit(code)
