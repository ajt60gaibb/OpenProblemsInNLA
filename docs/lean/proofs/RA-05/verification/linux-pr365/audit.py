#!/usr/bin/env python3
"""Independently audit the actual PR365 Linux receipt for eleven support proofs.

This reads original retained CI evidence and exact Git inputs. It does not
rerun Linux locally and does not prove the complete RA05 Target.
"""
import argparse,ast,datetime,gzip,hashlib,json,re,subprocess,zipfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
HEAD='0b0edfb8a75de34caec6c0f61cbf3193bbb15589'
MERGE='4c0220b702442c97e52ae98253169e6c759010bf'
BASE='5487945e5a72abd952b0c89915915de8cc9b3e65'
PROJECT='randomized-and-low-rank-approximation/RA-05/lean'
NAMES=['NLA.Proofs.RA05.SupportMinimum.'+n for n in ['rowCost_nonneg','cost_nonneg','strongCoreset_one','supportSize_one','minimumSupport_le_support','minimumSupport_attained','minimumSupport_le_rowCount','minimumSupport_le_worstSupport']]+['NLA.Proofs.RA05.'+n for n in ['unitHyperplane_projector','rowCost_unitHyperplane','strongCoreset_implies_allVectorEmbedding']]
ALLOWED=['propext','Classical.choice','Quot.sound']
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);args=p.parse_args();repo=args.repo.resolve()
 def git(*a):return subprocess.check_output(['git',*a],cwd=repo)
 def source(path,ref=HEAD):return git('show',ref+':'+path)
 checks=[]
 def check(name,passed,**evidence):checks.append({'name':name,'passed':bool(passed),**evidence})
 runs=json.loads((HERE/'commit-workflow-runs.json').read_text());artifacts=json.loads((HERE/'run-artifacts.json').read_text());jobs=json.loads((HERE/'run-jobs.json').read_text())
 run=next(x for x in runs['response']['workflow_runs'] if x['id']==39963923849)
 job=next(x for x in jobs['response']['jobs'] if x['id']==120449407972)
 artifact=next(x for x in artifacts['response']['artifacts'] if x['id']==12505618149)
 check('actual-workflow-terminal-success',run['status']=='completed' and run['conclusion']=='success' and runs['request']['commit_sha']==HEAD)
 check('actual-verification-job-terminal-success',job['status']=='completed' and job['conclusion']=='success' and job['run_id']==39963923849 and job['name']=='verify (RA-05, '+PROJECT+')')
 check('actual-validation-and-isolated-proof-steps-success',all(next(x for x in job['steps'] if x['name']==n)['conclusion']=='success' for n in ['Validate formalization manifest','Prepare unprivileged Linux isolation','Fresh sandboxed statement, axiom and kernel verification','Retain verification logs']))
 check('artifact-binds-real-run-and-head',artifact['workflow_run']['id']==39963923849 and artifact['workflow_run']['head_sha']==HEAD and artifact['name']=='lean-RA-05' and not artifact['expired'])
 rawrun=json.loads((HERE/'github-api-run.json').read_text());rawjobs=json.loads((HERE/'github-api-jobs.json').read_text());rawartifact=json.loads((HERE/'github-api-artifact-metadata.json').read_text())
 check('full-API-run-confirms-PR-head-and-terminal-success',rawrun['id']==39963923849 and rawrun['head_sha']==HEAD and rawrun['event']=='pull_request' and rawrun['status']=='completed' and rawrun['conclusion']=='success')
 rawjob=next(x for x in rawjobs['jobs'] if x['id']==120449407972)
 check('full-API-job-confirms-matching-success',rawjob['run_id']==39963923849 and rawjob['status']=='completed' and rawjob['conclusion']=='success' and rawjob['name']==job['name'])
 check('full-API-and-fresh-connector-artifact-metadata-agree',all(rawartifact[k]==artifact[k] for k in ['id','name','size_in_bytes','expired','digest','workflow_run']))
 archive=(HERE/'original-artifact.zip').read_bytes();archive_hash=sha(archive);job_raw=gzip.decompress((HERE/'job-120449407972.log.gz').read_bytes());job_text=job_raw.decode()
 check('original-zip-matches-fresh-GitHub-digest-and-size',artifact['digest']=='sha256:'+archive_hash and len(archive)==artifact['size_in_bytes']==16262,sha256=archive_hash)
 check('original-zip-matches-actual-job-upload-digest','SHA256 digest of uploaded artifact zip is '+archive_hash in job_text and 'Artifact lean-RA-05 has been successfully uploaded!' in job_text and 'Artifact ID 12505618149' in job_text)
 check('exact-original-uncompressed-job-log-sha256',sha(job_raw)=='071337faa483c1b90a514996609eb45ab095e6c676d006ad74711764eff5c2a0')
 check('actual-job-checked-synthetic-PR-merge',f'origin +{MERGE}:refs/remotes/pull/365/merge' in job_text and MERGE in job_text)
 parents=git('show','-s','--format=%P',MERGE).decode().strip().split()
 check('merge-has-exact-head-and-published-base-parents',parents==[BASE,HEAD],parents=parents)
 with zipfile.ZipFile(HERE/'original-artifact.zip') as z:
  safe=all(not Path(i.filename).is_absolute() and '..' not in Path(i.filename).parts and ((i.external_attr>>16)&0o170000)!=0o120000 for i in z.infolist())
  archived={n:sha(z.read(n)) for n in z.namelist() if not n.endswith('/')}
 extracted={str(q.relative_to(HERE/'artifact')):sha(q.read_bytes()) for q in (HERE/'artifact').rglob('*') if q.is_file()}
 check('safe-original-ZIP-and-exact-extraction',safe and archived==extracted,files=len(archived))
 result_paths=list((HERE/'artifact').rglob('result.json'));check('one-actual-completed-harness-result',len(result_paths)==1)
 result=json.loads(result_paths[0].read_text());logs=result_paths[0].parent
 check('actual-harness-execution-identity',result['repository_commit']==MERGE and result['project']==PROJECT)
 check('actual-comparator-accepted',result['result']=='comparator-accepted')
 check('actual-LeanCert-kernel-checked',result['lean_cert_proof_trust']=='kernel-checked' and result['verifier_profile']=='default')
 config={'challenge_module':'Challenge','solution_module':'Solution','theorem_names':NAMES,'definition_names':[],'permitted_axioms':ALLOWED}
 check('exact-eleven-support-exports-without-definition-holes',result['config']==config and all('Target' not in n and n!='NLA.Statements.RA05.Target' for n in NAMES))
 check('same-committed-Comparator-selection-at-head-and-merge',json.loads(source(PROJECT+'/comparator.json'))==json.loads(source(PROJECT+'/comparator.json',MERGE))==config)
 input_records=[]
 for rel,expected in result['input_sha256'].items():
  observed={'head':sha(source(PROJECT+'/'+rel)),'merge':sha(source(PROJECT+'/'+rel,MERGE)),'current':sha((repo/PROJECT/rel).read_bytes())}
  input_records.append({'path':rel,'expected_sha256':expected,'observed':observed,'passed':all(h==expected for h in observed.values())})
 check('all-forty-inputs-match-head-merge-and-current-package',len(input_records)==40 and all(i['passed'] for i in input_records),count=len(input_records))
 for ref,label in [(HEAD,'head'),(MERGE,'actual-CI-merge'),('HEAD','current-HEAD')]:
  names={n[len(PROJECT)+1:] for n in git('ls-tree','-r','--name-only','-z',ref,'--',PROJECT).decode().split('\0') if n}
  check('exact-40-file-project-set:'+label,names==set(result['input_sha256']),count=len(names))
 receipt=result['tool_receipt'];lock=source('tools/lean/source-lock.json',MERGE);lock_hash=sha(lock)
 check('exact-reviewed-checker-source-lock',lock_hash==result['source_lock_sha256']==receipt['source_lock_sha256']=='b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b')
 check('real-pinned-Linux-toolchain',receipt['lean_toolchain']=='leanprover/lean4:v4.33.1' and 'Linux' in receipt['platform'] and 'x86_64-unknown-linux-gnu' in receipt['lean_version'] and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in receipt['lean_version'])
 check('real-checker-exporter-sandbox-pins',receipt['forsythe_commit']==json.loads(lock)['commit']=='8d1b0c0545a77b40245e84705aa7d273e6c81e62' and set(receipt['executables'])=={'.tools/comparator/.lake/build/bin/comparator','.tools/lean4export/.lake/build/bin/lean4export','.tools/bin/landrun'} and all(re.fullmatch('[0-9a-f]{64}',s) for s in receipt['executables'].values()))
 tree=ast.parse(source('tools/lean/harness.py',MERGE));function=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='proof_trust_source')
 env={'MODULE':re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z"),'HarnessError':RuntimeError}
 exec(compile(ast.Module(body=[function],type_ignores=[]),'actual-committed-proof-trust-generator','exec'),env)
 audit=env['proof_trust_source'](config);(HERE/'ProofTrustAudit.generated.lean').write_text(audit)
 check('exact-actual-generated-proof-consumer',sha(audit.encode())==result['lean_cert_proof_trust_source_sha256'],sha256=sha(audit.encode()))
 check('consumer-checks-actual-theorem-kind-and-kernel-for-all-eleven','some (.thmInfo _)' in audit and 'set_option leancert.trust "kernel"' in audit and all('#assert_proof_constant '+n in audit and '#assert_trust kernel '+n in audit for n in NAMES))
 trust=(logs/'leancert-proof-trust.log').read_text();closures={n:[a.strip() for a in s.split(',')] for n,s in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",trust,re.S)}
 check('every-actual-proof-export-has-only-standard-three-axioms',set(closures)==set(NAMES) and all(set(a)==set(ALLOWED) for a in closures.values()),closures=closures)
 markers={
 'comparator.log':['Building Challenge','Building Solution','Exporting #[',' from Challenge',' from Solution','Running Lean default kernel on solution.','Lean default kernel accepts the solution','Your solution is okay!','scripts/strict_landrun.py','systemd-run --user','RestrictAddressFamilies=~AF_UNIX','EXIT_STATUS=0'],
 'kernel-controls.log':['RETURN honest_with_inductives_and_quotients: accepted','RETURN invalid_raw_proof: rejected','RETURN quotient_postcheck_mismatch: rejected','PASS: all three actual Comparator.runBuiltinKernel cases behaved as required','EXIT_STATUS=0'],
 'comparator-controls.log':['PASS simple_match: exit 0','PASS simple_mismatch: exit 1','PASS simple_axiom_issue: exit 1','PASS simple_kind_mismatch: exit 1','PASS type_mismatch: exit 1','PASS: all five Comparator regressions','EXIT_STATUS=0'],
 'sandbox.log':['MODE build: exit=0','MODE export: exit=0','PASS build .lake write: allowed','PASS export .lake write-open: denied','PASS symlink from .lake to outside write: denied','PASS host loopback listener: unreachable','PASS AF_UNIX socket creation: denied','PASS effective capabilities: none','PASS no_new_privs: set','PASS nested namespace write attempt: rejected','NEGATIVE unknown option: exit=2','NEGATIVE unexpected --rw: exit=2','NEGATIVE unexpected --rwx: exit=2','NEGATIVE relative --rwx: exit=2','Outer and export fixture contents unchanged; only designated build fixture written.','EXIT_STATUS=0'],
 'negative-sorry.log':["Illegal axiom detected: 'sorryAx'",'EXIT_STATUS=1'],
 'negative-native.log':["Illegal axiom detected: 'checked._native.native_decide.ax_1_1'",'EXIT_STATUS=1'],
 **{n:['EXIT_STATUS=0'] for n in ['leancert-build.log','leancert-proof-trust.log','dependencies.log','mathlib-cache.log','user-service.log']}}
 for name,required in markers.items():
  text=(logs/name).read_text();check('actual-log-controls:'+name,all(m in text for m in required),required=required)
 check('raw-job-final-real-harness-success','PASS: fresh Comparator run and all controls.' in job_text)
 for label,expected in {'SupportMinimum':'d21474d121f82481cf7de107ecaa8405d0b2d12cf60c08ef75fcbea471c1f0ce','HyperplaneDefinitions':'03c589f029a146203487f4d5ed5982eb67e4a91d64c0ab8f817baf1de898a276','HyperplaneBridge':'2e8d441f6aa46d7344c37762010be9e1afb30574e085bad980bb9bf01e7ccae1'}.items():
  check('exact-independently-reviewed-proof-bytes:'+label,sha(source(PROJECT+'/NLA/Proofs/RA05/'+label+'.lean'))==expected)
 check('full-original-Target-definition-retained',source(PROJECT+'/NLA/Statements/RA05.lean')==source('lean-statements/NLA/Statements/RA05.lean',BASE))
 check('original-canonical-page-retained-Solved',source('randomized-and-low-rank-approximation/RA-05/README.md')==source('randomized-and-low-rank-approximation/RA-05/README.md',BASE) and b'**Status:** Solved' in source('randomized-and-low-rank-approximation/RA-05/README.md'))
 check('permanent-ID-registry-retained',source('problem_ids.json')==source('problem_ids.json',BASE))
 check('package-truthfully-limits-proof-scope',all(t in source(PROJECT+'/README.md').decode() for t in ['Classification','NegativeAnswer','remains unproved']) and b'import Challenge' not in source(PROJECT+'/Solution.lean'))
 report={'reviewer':'OpenAI Codex AI agent /root/verification','date':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':__doc__,
 'head_commit':HEAD,'actual_execution_commit':MERGE,'merge_parents':parents,'run_id':39963923849,'job_id':120449407972,'artifact_id':12505618149,
 'checks':checks,'inputs':input_records,'archive_sha256':archive_hash,'job_log_uncompressed_sha256':sha(job_raw),'artifact_file_sha256':extracted,
 'evidence_sha256':{n:sha((HERE/n).read_bytes()) for n in ['commit-workflow-runs.json','run-artifacts.json','run-jobs.json','github-api-run.json','github-api-jobs.json','github-api-artifact-metadata.json','github-api-artifacts.json','original-artifact.zip','job-120449407972.log.gz','ProofTrustAudit.generated.lean']},
 'script_sha256':sha(Path(__file__).read_bytes()),'passed':all(c['passed'] for c in checks),'full_RA05_Target_proved':False,'linux_rerun_performed_locally':False}
 (HERE/'result.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'passed':report['passed'],'checks':len(checks),'inputs':len(input_records),'selected_support_theorems':len(NAMES),'failed':[c['name'] for c in checks if not c['passed']]},indent=2))
 return 0 if report['passed'] else 1
if __name__=='__main__':raise SystemExit(main())
