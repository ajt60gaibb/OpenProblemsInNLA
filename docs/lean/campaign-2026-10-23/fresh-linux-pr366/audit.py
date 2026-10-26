#!/usr/bin/env python3
"""Audit actual PR366 Linux full-proof artifacts with distinct head/merge identities.

No metadata is rewritten and no old strict checker's head-equals-execution
assumption is bypassed. This independently reads original evidence and Git.
"""
import argparse,ast,datetime,gzip,hashlib,json,re,subprocess,zipfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
HEAD='cc8f375f3d79ce7d3b7053526638ed37c9125e92'
MERGE='738e828fef5095e6f782a14bc68783a49a35212b'
BASE='5487945e5a72abd952b0c89915915de8cc9b3e65'
ORIGINAL='36767fa430309f13d04dc6ebe080d470f5c2444a'
PRIOR='42d1665800d0185581149ef494e03055b533d636'
RUN=39995308565
AXIOMS=['propext','Classical.choice','Quot.sound']
CASES=[('PF-05','PF05','nonnegative-and-positive-factorizations/PF-05/lean',120557399423,12519698144,90,46),
       ('SP-12','SP12','eigenvalues-and-inverse-problems/SP-12/lean',120557399244,12520885067,96,55),
       ('TR-14','TR14','tensor-computations/TR-14/lean',120557399236,12519239053,139,82)]
MARKERS={
 'comparator.log':['Building Challenge','Building Solution',' from Challenge',' from Solution','Running Lean default kernel on solution.','Lean default kernel accepts the solution','Your solution is okay!','scripts/strict_landrun.py','systemd-run --user','RestrictAddressFamilies=~AF_UNIX','EXIT_STATUS=0'],
 'kernel-controls.log':['RETURN honest_with_inductives_and_quotients: accepted','RETURN invalid_raw_proof: rejected','RETURN quotient_postcheck_mismatch: rejected','PASS: all three actual Comparator.runBuiltinKernel cases behaved as required','EXIT_STATUS=0'],
 'comparator-controls.log':['PASS simple_match: exit 0','PASS simple_mismatch: exit 1','PASS simple_axiom_issue: exit 1','PASS simple_kind_mismatch: exit 1','PASS type_mismatch: exit 1','PASS: all five Comparator regressions','EXIT_STATUS=0'],
 'sandbox.log':['MODE build: exit=0','MODE export: exit=0','PASS build .lake write: allowed','PASS export .lake write-open: denied','PASS symlink from .lake to outside write: denied','PASS host loopback listener: unreachable','PASS AF_UNIX socket creation: denied','PASS effective capabilities: none','PASS no_new_privs: set','PASS nested namespace write attempt: rejected','NEGATIVE unknown option: exit=2','NEGATIVE unexpected --rw: exit=2','NEGATIVE unexpected --rwx: exit=2','NEGATIVE relative --rwx: exit=2','Outer and export fixture contents unchanged; only designated build fixture written.','EXIT_STATUS=0'],
 'negative-sorry.log':["Illegal axiom detected: 'sorryAx'",'EXIT_STATUS=1'],
 'negative-native.log':["Illegal axiom detected: 'checked._native.native_decide.ax_1_1'",'EXIT_STATUS=1'],
 **{name:['EXIT_STATUS=0'] for name in ['leancert-build.log','leancert-proof-trust.log','dependencies.log','mathlib-cache.log','user-service.log']}}
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);args=ap.parse_args();repo=args.repo.resolve()
 def git(*a):return subprocess.check_output(['git',*a],cwd=repo)
 def source(path,ref=HEAD):return git('show',ref+':'+path)
 checks=[]
 def check(name,passed,**evidence):checks.append({'name':name,'passed':bool(passed),**evidence})
 runs=json.loads((HERE/'commit-workflow-runs.json').read_text());arts=json.loads((HERE/'run-artifacts.json').read_text());jobs=json.loads((HERE/'run-jobs.json').read_text());view=json.loads((HERE/'run-view.json').read_text())
 run=next(r for r in runs['response']['workflow_runs'] if r['id']==RUN)
 check('fresh-connector-workflow-success-for-exact-head',runs['request']['commit_sha']==HEAD and run['status']=='completed' and run['conclusion']=='success')
 check('authentic-run-view-confirms-distinct-PR-head',view['databaseId']==RUN and view['headSha']==HEAD and view['status']=='completed' and view['conclusion']=='success')
 parents=git('show','-s','--format=%P',MERGE).decode().strip().split()
 check('actual-merge-has-exact-base-and-head-parents',parents==[BASE,HEAD],parents=parents)
 registry=source('problem_ids.json');check('permanent-registry-byte-identity',registry==source('problem_ids.json',ORIGINAL))
 check('all-canonical-paths-retained',all((repo/p).is_file() for p in json.loads(registry).values()))
 tree=ast.parse(source('tools/lean/harness.py',MERGE));f=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='proof_trust_source')
 env={'MODULE':re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z"),'HarnessError':RuntimeError};exec(compile(ast.Module(body=[f],type_ignores=[]),'actual-PR366-proof-consumer-generator','exec'),env)
 prior=json.loads((HERE.parent/'verification/integration-and-preservation.json').read_text());check('prior-independent-original-preservation-audit-passed',prior['passed'] and prior['integration_commit']==PRIOR,receipt_sha256=sha((HERE.parent/'verification/integration-and-preservation.json').read_bytes()))
 cases={}
 for ident,label,project,job_id,artifact_id,count,lean_count in CASES:
  start=len(checks);directory=HERE/ident;target='NLA.'+label+'.target'
  def c(name,ok,**e):check(ident+':'+name,ok,**e)
  job=next(j for j in jobs['response']['jobs'] if j['id']==job_id);artifact=next(a for a in arts['response']['artifacts'] if a['id']==artifact_id)
  c('actual-verification-job-terminal-success',job['run_id']==RUN and job['name']=='verify ('+ident+', '+project+')' and job['status']=='completed' and job['conclusion']=='success')
  c('manifest-isolation-and-proof-steps-succeeded',all(next(s for s in job['steps'] if s['name']==n)['conclusion']=='success' for n in ['Validate formalization manifest','Prepare unprivileged Linux isolation','Fresh sandboxed statement, axiom and kernel verification','Retain verification logs']))
  c('artifact-binds-actual-run-and-PR-head',artifact['workflow_run']['id']==RUN and artifact['workflow_run']['head_sha']==HEAD and artifact['name']=='lean-'+ident and not artifact['expired'])
  archive=(directory/'original-artifact.zip').read_bytes();archive_hash=sha(archive);raw=gzip.decompress((directory/'job.log.gz').read_bytes());rawtext=raw.decode()
  c('original-archive-matches-fresh-GitHub-metadata',artifact['digest']=='sha256:'+archive_hash and artifact['size_in_bytes']==len(archive),sha256=archive_hash)
  c('original-archive-matches-real-upload-log','SHA256 digest of uploaded artifact zip is '+archive_hash in rawtext and 'Artifact lean-'+ident+' has been successfully uploaded!' in rawtext and 'Artifact ID '+str(artifact_id) in rawtext)
  c('raw-job-checkout-identifies-executed-PR-merge',f'origin +{MERGE}:refs/remotes/pull/366/merge' in rawtext)
  with zipfile.ZipFile(directory/'original-artifact.zip') as z:
   safe=all(not Path(i.filename).is_absolute() and '..' not in Path(i.filename).parts and ((i.external_attr>>16)&0o170000)!=0o120000 for i in z.infolist())
   zipped={n:sha(z.read(n)) for n in z.namelist() if not n.endswith('/')}
  extracted={str(q.relative_to(directory/'artifact')):sha(q.read_bytes()) for q in (directory/'artifact').rglob('*') if q.is_file()}
  c('safe-original-ZIP-and-exact-independent-extraction',safe and zipped==extracted,files=len(zipped))
  results=list((directory/'artifact').rglob('result.json'));c('one-completed-harness-result',len(results)==1)
  result=json.loads(results[0].read_text());logs=results[0].parent
  c('harness-identifies-actual-merge-and-project',result['repository_commit']==MERGE and result['project']==project)
  c('actual-full-proof-Comparator-and-LeanCert-acceptance',result['result']=='comparator-accepted' and result['lean_cert_proof_trust']=='kernel-checked' and result['verifier_profile']=='default')
  config={'challenge_module':'Challenge','solution_module':'Solution','theorem_names':[target],'definition_names':[],'permitted_axioms':AXIOMS}
  c('exact-single-full-Target-selection-no-holes',result['config']==config and json.loads(source(project+'/comparator.json'))==json.loads(source(project+'/comparator.json',MERGE))==config)
  records=[]
  for rel,expected in result['input_sha256'].items():
   observed={'PR_head':sha(source(project+'/'+rel)),'executed_merge':sha(source(project+'/'+rel,MERGE)),'current_package':sha((repo/project/rel).read_bytes()),'prior_reviewed_integration':sha(source(project+'/'+rel,PRIOR))}
   records.append({'path':rel,'expected_sha256':expected,'observed':observed,'passed':all(h==expected for h in observed.values())})
  c('all-actual-inputs-exact-at-head-merge-current-and-reviewed-integration',len(records)==count and all(i['passed'] for i in records),files=len(records))
  c('exact-reviewed-Lean-input-count',sum(i['path'].endswith('.lean') for i in records)==lean_count,lean_inputs=lean_count)
  for ref,ref_label in [(HEAD,'PR-head'),(MERGE,'executed-merge'),('HEAD','current-HEAD')]:
   names={n[len(project)+1:] for n in git('ls-tree','-r','--name-only','-z',ref,'--',project).decode().split('\0') if n}
   c('exact-project-file-set:'+ref_label,names==set(result['input_sha256']),files=len(names))
  receipt=result['tool_receipt'];lock=source('tools/lean/source-lock.json',MERGE)
  c('exact-reviewed-checker-source-lock',sha(lock)==result['source_lock_sha256']==receipt['source_lock_sha256']=='b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b')
  c('pinned-real-Linux-Lean-compiler',receipt['lean_toolchain']=='leanprover/lean4:v4.33.1' and 'Linux' in receipt['platform'] and 'x86_64-unknown-linux-gnu' in receipt['lean_version'] and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in receipt['lean_version'])
  c('pinned-checker-exporter-sandbox-identities',receipt['forsythe_commit']==json.loads(lock)['commit']=='8d1b0c0545a77b40245e84705aa7d273e6c81e62' and set(receipt['executables'])=={'.tools/comparator/.lake/build/bin/comparator','.tools/lean4export/.lake/build/bin/lean4export','.tools/bin/landrun'} and all(re.fullmatch('[0-9a-f]{64}',h) for h in receipt['executables'].values()))
  manifest=json.loads(source(project+'/lake-manifest.json'));pins={p['name']:p['rev'] for p in manifest['packages']}
  c('reviewed-LeanCert-and-Mathlib-pins',pins['leancert']=='621a43d7cf21f87872392a01e874f2f1dbddc926' and pins['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474')
  audit=env['proof_trust_source'](config);(directory/'ProofTrustAudit.generated.lean').write_text(audit)
  c('exact-actual-generated-theorem-kind-kernel-consumer',sha(audit.encode())==result['lean_cert_proof_trust_source_sha256'] and 'some (.thmInfo _)' in audit and '#assert_proof_constant '+target in audit and '#assert_trust kernel '+target in audit,sha256=sha(audit.encode()))
  trust=(logs/'leancert-proof-trust.log').read_text();closures={n:[a.strip() for a in s.split(',')] for n,s in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",trust,re.S)}
  c('actual-full-Target-proof-has-standard-three-axioms',closures.get(target)==AXIOMS,closures=closures)
  for name,required in MARKERS.items():c('actual-control-log:'+name,all(m in (logs/name).read_text() for m in required),required=required)
  c('actual-exporter-selected-full-theorem-twice',(logs/'comparator.log').read_text().count(target)>=2)
  c('actual-raw-job-has-final-harness-success','PASS: fresh Comparator run and all controls.' in rawtext)
  solution=source(project+'/Solution.lean');final=source(project+'/NLA/Proofs/'+label+'/Final.lean');statement=source(project+'/NLA/Statements/'+label+'.lean')
  c('literal-closed-full-Target-export-not-support-reduction',('theorem target : NLA.Statements.'+label+'.Target').encode() in solution and ('exact NLA.Proofs.'+label+'.target').encode() in solution and ('theorem target : NLA.Statements.'+label+'.Target').encode() in final and b'import Challenge' not in solution)
  c('original-reviewed-Target-definition-unchanged',statement==source('lean-statements/NLA/Statements/'+label+'.lean',ORIGINAL))
  proof_lock=json.loads(source(project+'/proof-source-lock.json'));copy_records=[]
  for item in proof_lock['copies']:
   a=sha(source(item['source']));b=sha(source(item['destination']));copy_records.append({'module':item['module'],'source_sha256':a,'destination_sha256':b,'passed':a==b==item['source_sha256']==item['destination_sha256']})
  c('all-reviewed-shared-proof-copies-exact',all(r['passed'] for r in copy_records),count=len(copy_records))
  canonical=json.loads(registry)[ident];original_paths=[canonical,'docs/lean/statements/'+ident+'/ORIGINAL.md']+[i['archive'] for i in prior['cases'][ident]['originals']]
  c('previously-audited-original-archives-and-canonical-history-unchanged',all(source(p)==source(p,PRIOR) for p in original_paths),paths=original_paths)
  c('no-changed-source-relabels-old-receipts',all(i['passed'] for i in records),prior_commit=PRIOR)
  case={'head_commit':HEAD,'actual_execution_commit':MERGE,'project':project,'target':target,'run_id':RUN,'job_id':job_id,'artifact_id':artifact_id,'archive_sha256':archive_hash,
   'job_log_uncompressed_sha256':sha(raw),'inputs':records,'reviewed_copies':copy_records,'artifact_file_sha256':extracted,
   'selected_target_statement_sha256':sha(statement),'final_proof_module_sha256':sha(final),'Solution_sha256':sha(solution),
   'checks':checks[start:],'passed':all(c['passed'] for c in checks[start:])}
  (directory/'audit.json').write_text(json.dumps(case,indent=2)+'\n');cases[ident]={'passed':case['passed'],'checks':len(case['checks']),'inputs':count,'lean_inputs':lean_count,'artifact_id':artifact_id,'archive_sha256':archive_hash,'audit_sha256':sha((directory/'audit.json').read_bytes())}
 report={'reviewer':'OpenAI Codex AI agent /root/verification','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':__doc__,
  'head_commit':HEAD,'actual_execution_commit':MERGE,'merge_parents':parents,'run_id':RUN,'cases':cases,'checks':checks,
  'passed':all(c['passed'] for c in checks),'metadata_sha256':{n:sha((HERE/n).read_bytes()) for n in ['commit-workflow-runs.json','run-artifacts.json','run-jobs.json','run-view.json']},
  'script_sha256':sha(Path(__file__).read_bytes()),'linux_rerun_performed_locally':False,'new_proof_sources_authored':False}
 (HERE/'result.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'passed':report['passed'],'checks':len(checks),'cases':cases,'failed':[c['name'] for c in checks if not c['passed']]},indent=2))
 return 0 if report['passed'] else 1
if __name__=='__main__':raise SystemExit(main())
