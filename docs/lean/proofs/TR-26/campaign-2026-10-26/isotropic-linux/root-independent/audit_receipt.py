#!/usr/bin/env python3
"""Independent offline audit of separately fetched original TR26 Linux bytes."""
import argparse,hashlib,json,re,subprocess,zipfile,io
from pathlib import Path,PurePosixPath
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--live',type=Path,required=True);p.add_argument('--author-evidence',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
checks=[];details={};error=None
sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda *v:subprocess.check_output(['git',*v],cwd=a.repo)
read=lambda ref,path:git('show',ref+':'+path)
load=lambda name:json.loads((a.live/name).read_text())
HEAD='6c607ab14af2b8b2b8075f0b3f1798e037c10899';BASE='ccc7864f5034cf7c4602f7577ceaf083ebf63d52';MERGE='71e8a941218a22a9c4f48f553b8e9767e7843349';CORRECTED='04045bad74f9dff03488b3b9080b081f397e5349';P='tensor-computations/TR-26/lean/';NAME='NLA.Proofs.TR26.isotropic_degree';AX={'propext','Classical.choice','Quot.sound'}
def check(name,condition):
 checks.append({'name':name,'passed':bool(condition)})
 if not condition:raise AssertionError(name)
try:
 run,job,art=[load(x) for x in ['run.json','job.json','artifact-metadata.json']]
 check('live-run-immutable-success',run['id']==40390314938 and run['head_sha']==HEAD and run['head_commit']['id']==HEAD and run['event']=='pull_request' and run['status']=='completed' and run['conclusion']=='success')
 check('live-job-exact-success',job['id']==121812956621 and job['run_id']==run['id'] and job['head_sha']==HEAD and job['conclusion']=='success')
 for step in ['Validate formalization manifest','Fresh sandboxed statement, axiom and kernel verification','Retain verification logs']:check('actual-job-step:'+step,any(s['name']==step and s['conclusion']=='success' for s in job['steps']))
 archive=(a.live/'original-artifact.zip').read_bytes();rawbytes=(a.live/'job-121812956621.log').read_bytes();raw=rawbytes.decode()
 check('live-original-artifact-digest-size',art['id']==12685225619 and art['name']=='lean-TR-26' and art['workflow_run']['id']==run['id'] and art['workflow_run']['head_sha']==HEAD and art['size_in_bytes']==len(archive)==26456 and art['digest']=='sha256:'+sha(archive) and not art['expired'])
 check('independent-ZIP-identical-to-author-original',archive==(a.author_evidence/'original-artifact.zip').read_bytes())
 check('independent-raw-log-identical-to-author-original',rawbytes==(a.author_evidence/'job-121812956621.log').read_bytes())
 check('raw-executed-merge-not-current-PR',MERGE in raw and 'HEAD is now at 71e8a941 Merge '+HEAD+' into '+BASE in raw and 'git checkout --progress --force refs/remotes/pull/369/merge' in raw)
 check('executed-merge-parents',git('show','-s','--format=%P',MERGE).decode().split()==[BASE,HEAD])
 check('raw-upload-artifact-ID-digest',f'Artifact ID {art["id"]}' in raw and 'SHA256 digest of uploaded artifact zip is '+sha(archive) in raw)
 with zipfile.ZipFile(io.BytesIO(archive)) as z:
  check('ZIP-integrity',z.testzip() is None)
  names=z.namelist();check('ZIP-safe-unique-members',len(names)==len(set(names)) and all(not PurePosixPath(n).is_absolute() and '..' not in PurePosixPath(n).parts and '\\' not in n for n in names))
  members={n:z.read(n) for n in names}
 resultpaths=[n for n in names if n.endswith('/result.json')];check('one-harness-receipt',len(resultpaths)==1)
 prefix=resultpaths[0][:-len('result.json')];r=json.loads(members[resultpaths[0]])
 check('actual-receipt-source-project-and-acceptance',r['repository_commit']==MERGE and r['project']==P.rstrip('/') and r['result']=='comparator-accepted' and r['lean_cert_proof_trust']=='kernel-checked')
 cfg=r['config'];check('one-real-theorem-and-no-definition-holes',cfg=={'challenge_module':'Challenge','solution_module':'Solution','theorem_names':[NAME],'definition_names':[],'permitted_axioms':['propext','Classical.choice','Quot.sound']})
 paths=git('ls-tree','-r','--name-only',HEAD,P).decode().splitlines();inputs=r['input_sha256'];lock=json.loads(read(HEAD,P+'PACKAGE_LOCK.json'))
 check('354-exact-input-set',len(inputs)==len(paths)==354 and set(inputs)=={q[len(P):] for q in paths})
 check('353-reviewed-lock-entries',len(lock['files'])==353 and set(lock['files'])==set(inputs)-{'PACKAGE_LOCK.json'})
 for q,h in inputs.items():
  b=read(HEAD,P+q);check('CI-head-merge-corrected-source:'+q,sha(b)==h and b==read(MERGE,P+q)==read(CORRECTED,P+q))
  if q in lock['files']:check('package-lock-source:'+q,lock['files'][q]=={'sha256':h,'bytes':len(b)})
 check('40-runtime-sources',len([q for q in inputs if q.endswith('.lean') and not q.startswith('reviews/')])==40)
 sm=json.loads(read(HEAD,P+'SOURCE_MAP.json'));check('117-source-mappings',len(sm['copies'])==117)
 for rec in sm['copies']:
  b=read(rec['source_ref'],rec['source_path']);check('exact-provenance:'+rec['path'],sha(b)==rec['sha256']==inputs[rec['path']] and len(b)==rec['bytes'])
 tool=r['tool_receipt'];check('actual-official-Linux-Lean',tool['lean_version']=='Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)' and tool['lean_version'] in raw and tool['platform'].startswith('Linux-') and tool['go_version']=='go version go1.27.1 linux/amd64')
 check('actual-pinned-checker-and-source-lock',tool['forsythe_commit']=='8d1b0c0545a77b40245e84705aa7d273e6c81e62' and tool['source_lock_sha256']==r['source_lock_sha256']==sha(read(MERGE,'tools/lean/source-lock.json')))
 log=lambda n:members[prefix+n+'.log'].decode()
 expected='\n'.join(['import Solution','import LeanCert.Tactic.Verification','set_option autoImplicit false','set_option leancert.trust "kernel"','','open Lean Elab Command in','elab "#assert_proof_constant " n:ident : command => do','  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n','  match (← getEnv).find? decl with','  | some (.thmInfo _) => pure ()','  | _ => throwErrorAt n "expected a proved theorem constant"','','#assert_proof_constant '+NAME,'#assert_trust kernel '+NAME,'#print axioms '+NAME])+'\n'
 check('independent-exact-kind-kernel-consumer',sha(expected.encode())==r['lean_cert_proof_trust_source_sha256'])
 ax=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log('leancert-proof-trust'));check('actual-transitive-standard-axioms',len(ax)==1 and ax[0][0]==NAME and {s.strip() for s in ax[0][1].split(',')}==AX)
 exports=[line for line in log('comparator').splitlines() if line.startswith('Exporting #[')];check('actual-reference-solution-signature-exports',len(exports)==2 and all(re.findall(r'NLA\.Proofs\.TR26\.[A-Za-z_]+',x)==[NAME] for x in exports) and exports[0].endswith('from Challenge') and exports[1].endswith('from Solution'))
 for token in ['Building Challenge','Building Solution','Lean default kernel accepts the solution','Your solution is okay!']:check('actual-Comparator:'+token,token in log('comparator'))
 for token in ['RETURN honest_with_inductives_and_quotients: accepted','RETURN invalid_raw_proof: rejected:','(kernel) declaration type mismatch','RETURN quotient_postcheck_mismatch: rejected:','Quotient post-check rejects the solution','PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:check('actual-raw-kernel-control:'+token,token in log('kernel-controls'))
 check('actual-five-Comparator-controls','PASS: all five Comparator regressions' in log('comparator-controls'))
 check('actual-sorry-and-native-rejections',"Illegal axiom detected: 'sorryAx'" in log('negative-sorry') and "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'" in log('negative-native'))
 for token in ['outside .lake write-open: denied','outside .lake truncate: denied','outside .lake creation: denied','symlink from .lake to outside write: denied','user namespace: private','pid namespace: private','mnt namespace: private','net namespace: private','ipc namespace: private','uts namespace: private','host parent: absent from private /proc','host parent signal lookup: denied','host loopback listener: unreachable','AF_UNIX socket creation: denied','effective capabilities: none','no_new_privs: set','nested namespace write attempt: rejected']:check('both-real-isolation-modes:'+token,log('sandbox').count('PASS '+token)==2)
 check('actual-build-export-access-policy',all(t in log('sandbox') for t in ['MODE build: exit=0','MODE export: exit=0','PASS build .lake write: allowed','PASS export .lake write-open: denied','PASS export .lake truncate: denied']))
 for token in ['unknown option','unexpected --rw','unexpected --rwx','relative --rwx']:check('actual-sandbox-option-control:'+token,'NEGATIVE '+token+': exit=2' in log('sandbox'))
 pins={x['name']:x['rev'] for x in json.loads(read(HEAD,P+'lake-manifest.json'))['packages']};check('10-pinned-dependencies',len(pins)==10 and pins['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474' and pins['leancert']=='621a43d7cf21f87872392a01e874f2f1dbddc926')
 for name,rev in pins.items():check('actual-pin:'+name,"checking out revision '"+rev+"'" in log('dependencies'))
 rawlines=[re.sub(r'^\ufeff?\d{4}-\d\d-\d\dT[^ ]+Z ','',x) for x in raw.splitlines()]
 for name,b in members.items():
  if not name.endswith('.log'):continue
  lines=b.decode().splitlines();status=1 if name.endswith(('negative-native.log','negative-sorry.log')) else 0
  check('log-exit:'+name,lines[-1]=='EXIT_STATUS='+str(status))
  check('raw-executed-command:'+name,lines[0].startswith('$ ') and 'Running '+lines[0][2:] in rawlines)
  pos=0
  for line in lines[1:]:
   if line and not line.startswith('EXIT_STATUS='):pos=rawlines.index(line,pos)+1
  check('every-artifact-body-line-in-independent-raw-log:'+name,True)
 formal=json.loads(read(HEAD,P+'formalization.yaml'));check('no-full-problem-promotion-claim',formal['status']['whole_problem_verified'] is False and formal['status']['canonical_status']=='Solved' and [x['declaration'] for x in formal['status']['main_results']]==[NAME])
 pre=json.loads(read(HEAD,'docs/lean/proofs/TR-26/campaign-2026-10-26/preproof/INPUT_LOCK.json'))
 for rec in pre['reviewed_inputs']:check('unchanged-original:'+rec['path'],sha(read(HEAD,rec['path']))==rec['sha256'] and read(HEAD,rec['path'])==read(MERGE,rec['path']))
 check('full-original-canonical-README-and-copy',read(HEAD,'tensor-computations/TR-26/README.md')==read(HEAD,P+'sources/ORIGINAL.md')==read(HEAD,'docs/lean/statements/TR-26/ORIGINAL.md'))
 check('217-original-ID-path-pairs',len(json.loads(read(HEAD,'problem_ids.json')))==217 and read(HEAD,'problem_ids.json')==read(BASE,'problem_ids.json'))
 details={'run':run['id'],'job':job['id'],'artifact':art['id'],'source_head':HEAD,'executed_merge':MERGE,'base':BASE,'package_inputs':354,'locked_inputs':353,'runtime_sources':40,'selected_theorems':[NAME],'archive_sha256':sha(archive),'archive_bytes':len(archive),'raw_log_sha256':sha(rawbytes),'raw_log_bytes':len(rawbytes),'receipt_sha256':sha(members[resultpaths[0]]),'tool_receipt':tool}
except Exception as exc:error=str(exc)
a.output.mkdir(parents=True,exist_ok=True)
r={'reviewer':'/root','role':'Independent audit of author-collected Linux receipt; root is a proof author, so this is not independent final source review.','passed':error is None,'error':error,'check_count':len(checks),'checks':checks,'driver_sha256':sha(Path(__file__).read_bytes()),'limits':['Covers the exact isotropic endpoint only. Full Target requires separate source/package reviews and a new Linux receipt.','Uses separately re-fetched original GitHub ZIP/raw job bytes, not current mutable PR head/merge metadata.','Offline audit runs no Lean, sandbox, Comparator or new Linux job.'],**details}
(a.output/'ROOT_CI_AUDIT.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['passed','error','check_count','driver_sha256']},indent=2));raise SystemExit(0 if r['passed'] else 1)
