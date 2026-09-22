from pathlib import Path
import datetime,hashlib,json,os,platform,subprocess,tarfile
base=Path('/home/admin/nla-tr27-full-20260922');repo=base/'repo';preparation=json.loads((base/'preparation.json').read_text());receipt=json.loads((base/'input-receipt.json').read_text())
runner=json.loads((base/'runner-result-attempt-1.json').read_text());assert runner['status']=='finished' and runner['exit_code']==0
logs=Path('/home/admin/nla-lean-tools/logs/verify-20260922T192408Z-961');result=json.loads((logs/'result.json').read_text())
assert result['result']=='comparator-accepted' and result['repository_commit']==preparation['guest_repository_commit']
assert result['input_sha256']==receipt['input_sha256'] and result['config']['theorem_names']==receipt['theorem_names']
project=repo/receipt['project_path'];actual={str(p.relative_to(project)):hashlib.sha256(p.read_bytes()).hexdigest() for p in project.rglob('*') if p.is_file()};assert actual==receipt['input_sha256']
status=subprocess.check_output(['git','status','--porcelain'],cwd=repo,text=True);assert not status
unit=subprocess.run(['systemctl','--user','show','nla-tr27-full-20260922-r1.service','--property=ActiveState,SubState,Result,ExecMainCode,ExecMainStatus,LimitNOFILE,RuntimeMaxUSec'],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
provenance={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'operator_role':'mechanical operator, also ProjectiveGeometry author; not an independent final referee','publication_commit':receipt['publication_commit'],'guest_repository_commit':result['repository_commit'],'commit_relation':preparation['commit_relation'],'git_status_after_verification':status,'all116_inputs_unchanged_after_verification':True,'uid':os.getuid(),'kernel':platform.platform(),'apparmor_userns_setting':subprocess.check_output(['sysctl','kernel.apparmor_restrict_unprivileged_userns'],text=True).strip(),'successful_log_directory':str(logs),'result':result['result'],'project':result['project'],'selected_theorem_count':len(result['config']['theorem_names']),'systemd_service':{'unit':'nla-tr27-full-20260922-r1.service','query_exit':unit.returncode,'properties':unit.stdout},'failed_verification_attempts':0,'note':'Fresh dependencies, separate module builds/exports and all controls were executed by the unchanged shared harness. Intermediate export streams are managed and removed by pinned Comparator; full export declaration lists and results are retained in comparator.log.'}
(base/'execution-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
archive=base/'verification-evidence.tar.gz';assert not archive.exists()
with tarfile.open(archive,'w:gz') as t:
 t.add(logs,arcname='successful-verification')
 t.add(project,arcname='source')
 for name in ['verification-driver-attempt-1.log','runner-result-attempt-1.json','preparation.json','run-verifier.py','input-receipt.json','execution-provenance.json','dependency-evidence']:
  t.add(base/name,arcname=name)
 t.add('/home/admin/nla-lean-tools/bootstrap.json',arcname='bootstrap.json')
 for f in sorted(Path('/home/admin/mf21-harness/tools/lean').iterdir()):
  if f.is_file() and f.suffix in {'.py','.json','.md','.sh'}:t.add(f,arcname='checker-source/'+f.name)
 for source,target in [('scripts/strict_landrun.py','strict_landrun.py'),('reproduction/checks/sandbox_probe_ci.py','sandbox_probe_ci.py'),('.tools/env.sh','env.sh')]:
  t.add(Path('/home/admin/nla-lean-tools')/source,arcname='checker-runtime-source/'+target)
meta={'path':str(archive),'bytes':archive.stat().st_size,'sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'publication_commit':receipt['publication_commit'],'guest_repository_commit':result['repository_commit'],'input_count':len(actual),'theorem_count':len(result['config']['theorem_names']),'result':result['result']}
(base/'evidence-export-receipt.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta,indent=2))
