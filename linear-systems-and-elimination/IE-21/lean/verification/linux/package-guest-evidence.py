from pathlib import Path
import datetime,hashlib,json,os,platform,subprocess,tarfile
base=Path(__file__).resolve().parent;repo=base/'repo'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
preparation=json.loads((base/'preparation.json').read_text());receipt=json.loads((base/'input-receipt.json').read_text())
runners=[json.loads(p.read_text()) for p in sorted(base.glob('runner-result-attempt-*.json'))]
assert runners and all(r['status']=='finished' for r in runners)
runner=runners[-1];assert runner['exit_code']==0 and runner['dependency_capture_succeeded']
assert len(runner['verification_log_directories'])==1
logs=Path(runner['verification_log_directories'][0]);result=json.loads((logs/'result.json').read_text())
assert result['result']=='comparator-accepted' and result['repository_commit']==preparation['guest_repository_commit']
assert result['input_sha256']==receipt['input_sha256'] and result['config']['theorem_names']==receipt['theorem_names']
project=repo/receipt['project_path']
actual={str(p.relative_to(project)):sha(p) for p in project.rglob('*') if p.is_file()};assert actual==receipt['input_sha256']
status=subprocess.check_output(['git','status','--porcelain'],cwd=repo,text=True);assert not status
unit='nla-ie21-full-20260922-r1.service'
service=subprocess.run(['systemctl','--user','show',unit,'--property=ActiveState,SubState,Result,ExecMainCode,ExecMainStatus,LimitNOFILE,RuntimeMaxUSec'],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
journal=subprocess.run(['journalctl','--user','-u',unit,'--no-pager','-o','short-iso'],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
lifecycle={'unit':unit,'query_exit':service.returncode,'post_completion_properties':service.stdout,'journal_exit':journal.returncode,'journal':journal.stdout,'interpretation':'The detached transient unit may unload after completion; default properties from an unloaded unit do not measure its former live limits. Requested limits are retained in host service-start.json. Fresh sandbox controls are the verification policy evidence.'}
(base/'service-lifecycle.json').write_text(json.dumps(lifecycle,indent=2)+'\n')
provenance={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'operator_role':'Mechanical operator, author of separate IE-21 Gaussian/spherical modules; not an independent final referee','publication_commit':receipt['publication_commit'],'guest_repository_commit':result['repository_commit'],'commit_relation':preparation['commit_relation'],'git_status_after_verification':status,'all_inputs_unchanged_after_verification':True,'input_count':len(actual),'uid':os.getuid(),'kernel':platform.platform(),'apparmor_userns_setting':subprocess.check_output(['sysctl','kernel.apparmor_restrict_unprivileged_userns'],text=True).strip(),'successful_log_directory':str(logs),'result':result['result'],'project':result['project'],'selected_theorem_count':len(result['config']['theorem_names']),'failed_verification_attempts':sum(r['exit_code']!=0 for r in runners),'host_preparation_issues_before_verification':1,'note':'Fresh dependencies, separate module builds/exports and all controls executed by unchanged shared harness. A read-only wrapper observer captured exact snapshot source and dependency Git heads. Intermediate export streams are removed by pinned Comparator; actual export declaration lists and results are retained in comparator.log.'}
(base/'execution-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
archive=base/'verification-evidence.tar.gz';assert not archive.exists()
with tarfile.open(archive,'w:gz') as t:
 t.add(logs,arcname='successful-verification')
 t.add(project,arcname='source')
 for name in ['preparation.json','input-receipt.json','execution-provenance.json','dependency-evidence','service-lifecycle.json']:
  t.add(base/name,arcname=name)
 for p in sorted(base.iterdir()):
  if p.is_file() and (p.suffix=='.py' or p.name.startswith(('verification-driver-attempt-','runner-result-attempt-','dependency-capture-attempt-'))):t.add(p,arcname=p.name)
 for i,r in enumerate(runners[:-1],1):
  for j,path in enumerate(r['verification_log_directories'],1):t.add(path,arcname=f'failed-verification-attempt-{i}-logs-{j}')
 t.add('/home/admin/nla-lean-tools/bootstrap.json',arcname='bootstrap.json')
 for f in sorted(Path('/home/admin/mf21-harness/tools/lean').iterdir()):
  if f.is_file() and f.suffix in {'.py','.json','.md','.sh'}:t.add(f,arcname='checker-source/'+f.name)
 for source,target in [('scripts/strict_landrun.py','strict_landrun.py'),('reproduction/checks/sandbox_probe_ci.py','sandbox_probe_ci.py'),('.tools/env.sh','env.sh')]:
  t.add(Path('/home/admin/nla-lean-tools')/source,arcname='checker-runtime-source/'+target)
meta={'path':str(archive),'bytes':archive.stat().st_size,'sha256':sha(archive),'publication_commit':receipt['publication_commit'],'guest_repository_commit':result['repository_commit'],'input_count':len(actual),'theorem_count':len(result['config']['theorem_names']),'result':result['result']}
(base/'evidence-export-receipt.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta,indent=2))
