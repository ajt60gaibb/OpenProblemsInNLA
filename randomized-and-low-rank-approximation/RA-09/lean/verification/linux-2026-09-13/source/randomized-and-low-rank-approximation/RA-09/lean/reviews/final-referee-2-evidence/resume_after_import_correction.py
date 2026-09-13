"""Focused referee2 resume after the retained import-order diagnostic.
Reuses only this reviewer's own hash-verified fresh target objects.
"""
from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,time,traceback
E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
prior=json.loads((E/'fresh-result.json').read_text());prefix=Path(prior['prefix'])
assert prior['verdict']=='FAIL' and prior['commands'][-1]['source'].endswith('/Inspect.lean')
assert 'invalid' in (E/prior['commands'][-1]['log']).read_text()
for row in prior['objects_hashed_before_cleanup']:
 assert sha(prefix/row['path'])==row['sha256'] and (prefix/row['path']).stat().st_size==row['bytes']
for row in prior['commands'][:-1]:
 assert row['exit_code']==0 and sha(P/row['source'])==row['source_sha256']
freeze=json.loads((P/'verification/proof-freeze.json').read_text())
assert sha(P/'verification/proof-freeze.json')=='533f5c328cdaf8c1f23f238f8c71b7b4b2fdabb2f532d58a398d4ab2434ccf7e'
for name,h in freeze['files'].items():assert sha(P/name)==h,name
env=os.environ.copy();env['LEAN_PATH']=prior['LEAN_PATH']
L=Path(prior['commands'][0]['command'][0])
sources=['reviews/final-referee-2-evidence/Inspect.lean','reviews/final-referee-2-evidence/Consumer.lean']
record={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'/root/mf16_final_referee',
 'platform':prior['platform'],'scope':prior['scope'],'prefix':str(prefix),'LEAN_PATH':env['LEAN_PATH'],
 'prior_result_sha256':sha(E/'fresh-result.json'),'verified_prior_successful_commands':len(prior['commands'])-1,
 'verified_own_private_objects':len(prior['objects_hashed_before_cleanup']),
 'runner_sha256':sha(__file__),'commands':[],'verdict':'RUNNING'}
def save():(E/'resume-result.json').write_text(json.dumps(record,indent=2)+'\n')
save()
try:
 for source in sources:
  f=P/source;stem=Path(source).stem+'-retry'
  snapshot=E/(stem+'.lean.txt');snapshot.write_bytes(f.read_bytes())
  target=prefix/Path(source).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(L),'-o',str(target),'-i',str(target.with_suffix('.ilean')),str(f)]
  t=time.monotonic();r=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
  log=E/(stem+'.log');log.write_bytes(r.stdout+r.stderr)
  row={'source':source,'source_sha256':sha(f),'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-t,
   'log':log.name,'log_sha256':sha(log),'source_snapshot':snapshot.name}
  record['commands'].append(row);save();print(source,r.returncode,round(row['seconds'],2),flush=True)
  assert r.returncode==0 and 'error:' not in log.read_text() and 'warning:' not in log.read_text(),log
  for ax in re.findall(r'depends on axioms: \[(.*?)\]',log.read_text()):
   assert set(x.strip() for x in ax.split(','))<={'propext','Classical.choice','Quot.sound'},ax
 pins=[]
 for item in prior['pins']:
  dep=Path(item['path']);rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=dep).decode().strip()
  status=subprocess.check_output(['git','status','--porcelain=v1'],cwd=dep).decode()
  assert rev==item['rev'] and not status
  pins.append({**item,'rev':rev,'status':status})
 assert pins==prior['pins']
 (E/'dependency-pins-after.json').write_text(json.dumps(pins,indent=2)+'\n')
 for name,h in freeze['files'].items():assert sha(P/name)==h,name
 for name,h in freeze['source_files'].items():
  raw=subprocess.check_output(['git','show',freeze['base']+':'+name],cwd=W)
  assert hashlib.sha256(raw).hexdigest()==h and (W/name).read_bytes()==raw,name
  assert subprocess.check_output(['git','rev-parse',freeze['base']+':'+name],cwd=W).decode().strip()==freeze['source_git_blobs'][name]
 before=json.loads((E/'integrity-before.json').read_text())
 (E/'integrity-after.json').write_text(json.dumps(before,indent=2)+'\n')
 record['verdict']='PASS'
except BaseException as exc:
 record['verdict']='FAIL';record['failure']=repr(exc)
 (E/'resume-raw-failure.txt').write_text(traceback.format_exc());raise
finally:
 record['objects_hashed_before_cleanup']=[{'path':str(f.relative_to(prefix)),'bytes':f.stat().st_size,'sha256':sha(f)} for f in sorted(prefix.rglob('*')) if f.is_file()]
 if record['verdict']=='PASS':
  shutil.rmtree(prefix);record['disposable_prefix_removed_after_check']=True
 else:record['disposable_prefix_removed_after_check']=False
 record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
print('PASS: fresh reviewer inspector and literal norm/CFC consumer',flush=True)
