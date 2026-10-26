#!/usr/bin/env python3
"""Offline read-only audit of original TR04 final-promotion Linux ZIP/raw-job/API bytes.

Only the requested JSON report beneath this audit directory is written. No
network, checkout, extraction, Lean, Comparator, shell or proof code is run.
"""
import argparse, ast, functools, gzip, hashlib, io, json, pathlib, re, subprocess, zipfile

HERE=pathlib.Path(__file__).resolve().parent
PROJECT='tensor-computations/TR-04/lean'
HEAD='09cd782576559502787fb536bc1427bf64b7b3e4'
CANDIDATE='027aaefbadf602ac460d0cf4cae7beed3181d712'
BASE='01141f415715a27473cabc1f35ef898e86aafae2'
RUN=40408919808
EXPECTED_JOB=121875088207
PR=370
DOC='docs/lean/proofs/TR-04/campaign-2026-10-26/'
FREEZE=DOC+'CANONICAL_PROMOTION_FREEZE_2026-10-26.json'
FREEZE_SHA='44b5df77ea7ed70c35aac6e87b2001f2b6860a36f58f1156a50d01a3c83374f7'
APPROVAL=DOC+'independent-promotion-source-algebra/APPROVAL.json'
APPROVAL_SHA='cd73378761ccbb3136ace67f3ce7132785f92b6e6663658e2745428eb075ce33'
PROPOSAL=DOC+'promotion-draft/PROMOTION_PROPOSAL.json'
PROPOSAL_SHA='c352fedca0c34cf23c89e41fdc82cb870ff552b5d50c6fe01a1fc6b5d47a11b0'
ORIGINAL_ARCHIVE=DOC.removesuffix('campaign-2026-10-26/')+'originals-before-full-proof-2026-10-26/manifest.json'
ORIGINAL_ARCHIVE_SHA='81d4086ffcbc92eb2b1c92f815ed1d859f2393d0b47d2fca0c3275968d308047'
NAMES=['candidate_count_le_first_mode','cyclic_window_count_le_first_mode','NLA.TR04.target']
STANDARD=['propext','Classical.choice','Quot.sound']
EXPECTED_AXIOMS={NAMES[0]:[],NAMES[1]:[],NAMES[2]:STANDARD}
CONFIG=dict(challenge_module='FullChallenge',solution_module='FullSolution',theorem_names=NAMES,definition_names=[],permitted_axioms=STANDARD)
PINNED_TOOL_FILES={'.github/workflows/lean-verification.yml':'850fd6f1155f62b3ad0a9636e0613b0bc2c20f81efe60424ad01f3f89053b453','tools/lean/harness.py':'175e77ebf398849ee20195d126c6b7e8b040111fed1086fe7f1ad1e36cc5eae1','tools/lean/source-lock.json':'b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b'}
sha=lambda b:hashlib.sha256(b).hexdigest()

def unique(pairs):
 d={}
 for k,v in pairs:
  if k in d:raise ValueError('Duplicate JSON key: '+k)
  d[k]=v
 return d

def decode(b):return json.loads(b,object_pairs_hook=unique)

def header(text,name):
 a=text.index('theorem '+name);return ' '.join(text[a:text.index(':=',a)].split())

def axiom_records(text):
 # Lean prints a distinct sentence for an empty transitive axiom set.
 matches=re.findall(r"'([^']+)' (?:(does not depend on any axioms)|depends on axioms:\s*\[([^\]]*)\])",text)
 return [(name,[] if empty else [x.strip() for x in body.split(',') if x.strip()]) for name,empty,body in matches]

def selected_exports(line):
 # Comparator also exports its fixed Quot and kernel primitive constants.
 inside=line.split('#[',1)[1].split(']',1)[0]
 tokens=[x.strip() for x in inside.split(',')]
 fixed={'Quot','Quot.mk','Quot.lift','Quot.ind','propext','Classical.choice','Quot.sound','Nat.add','Nat.sub','Nat.mul','Nat.pow','Nat.gcd','Nat.div','Nat.mod','Nat.beq','Nat.ble','Nat.land','Nat.lor','Nat.xor','Nat.shiftLeft','Nat.shiftRight','String.ofList','Char.ofNat','List','eagerReduce','Nat','String','String.mk','Char','optParam','autoParam','semiOutParam','outParam'}
 if len(tokens)!=len(set(tokens)) or not set(tokens)<=fixed|set(NAMES):return None
 return [x for x in tokens if x in NAMES]

def proof_consumer():
 lines=['import FullSolution','import LeanCert.Tactic.Verification','set_option autoImplicit false','set_option leancert.trust "kernel"','','open Lean Elab Command in','elab "#assert_proof_constant " n:ident : command => do','  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n','  match (← getEnv).find? decl with','  | some (.thmInfo _) => pure ()','  | _ => throwErrorAt n "expected a proved theorem constant"','']
 for n in NAMES:lines += ['#assert_proof_constant '+n,'#assert_trust kernel '+n,'#print axioms '+n]
 return '\n'.join(lines)+'\n'

def probe_source(source):
 replacements=[('"--pty"','"--pipe"',2),('"--property=RestrictAddressFamilies=~AF_UNIX"','"--property=RestrictAddressFamilies=~AF_UNIX", "--property=RuntimeMaxSec=40"',2),('subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)','subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=45)',2),('\n                result = subprocess.run(command','\n                print(f"START sandbox mode: {mode}", flush=True)\n                result = subprocess.run(command',1),('\n            result = subprocess.run(command','\n            print(f"START sandbox negative case: {label}", flush=True)\n            result = subprocess.run(command',1),('landrun_args = ["--best-effort", "--ro", "/",','landrun_args = ["--best-effort", "--rox", "/usr/bin/bwrap", "--ro", "/",',1)]
 for old,new,count in replacements:
  if source.count(old)!=count:raise ValueError('CI probe adaptation source mismatch')
  source=source.replace(old,new)
 return source

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=pathlib.Path,default=HERE.parents[5])
 for name in ['run-json','jobs-json','artifacts-json','artifact-metadata','archive','job-log']:
  p.add_argument('--'+name,type=pathlib.Path,required=True)
 p.add_argument('--job-log-gz',type=pathlib.Path)
 p.add_argument('--job',type=int,required=True);p.add_argument('--artifact',type=int,required=True)
 p.add_argument('--output',type=pathlib.Path,required=True)
 a=p.parse_args();repo=a.repo.resolve();output=a.output.resolve()
 if not output.is_relative_to(HERE) or output==pathlib.Path(__file__).resolve():raise ValueError('Report must be a new path beneath this audit directory')
 if output.exists() or not output.parent.is_dir():raise ValueError('Report must not overwrite any file; its parent must exist')
 evidence_paths=[getattr(a,n) for n in ['run_json','jobs_json','artifacts_json','artifact_metadata','archive','job_log']]+([a.job_log_gz] if a.job_log_gz else [])
 if any(x.resolve()==output for x in evidence_paths):raise ValueError('Report aliases an input')
 evidence_hashes={str(x.resolve()):sha(x.read_bytes()) for x in evidence_paths}
 checks=[];details={};error=None;reader=None
 def check(name,ok,**extra):
  checks.append(dict(name=name,passed=bool(ok),**extra))
  if not ok:raise AssertionError(name)
 def git(*args):return subprocess.check_output(['git',*args],cwd=repo)
 @functools.lru_cache(None)
 def blob(ref,path):
  if '\n' in ref+path or '\r' in ref+path:raise ValueError('Invalid Git object key')
  reader.stdin.write((ref+':'+path+'\n').encode());reader.stdin.flush()
  h=reader.stdout.readline().decode().rstrip('\n').split()
  if len(h)!=3 or h[1]!='blob':raise ValueError('Missing immutable Git blob '+ref+':'+path)
  n=int(h[2]);b=reader.stdout.read(n)
  if len(b)!=n or reader.stdout.read(1)!=b'\n':raise ValueError('Truncated Git object')
  return b
 def tree(ref):return {q.removeprefix(PROJECT+'/') for q in git('ls-tree','-r','--name-only',ref,'--',PROJECT).decode().splitlines()}
 try:
  reader=subprocess.Popen(['git','cat-file','--batch'],cwd=repo,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  run=decode(a.run_json.read_bytes());jobs=decode(a.jobs_json.read_bytes());listing=decode(a.artifacts_json.read_bytes());art=decode(a.artifact_metadata.read_bytes())
  check('fixed-run-PR370-head-terminal-success',run['id']==RUN and run['head_sha']==HEAD and run['head_commit']['id']==HEAD and run['event']=='pull_request' and run['status']=='completed' and run['conclusion']=='success' and run['run_attempt']==1 and any(x['number']==PR for x in run['pull_requests']))
  selected=[x for x in jobs['jobs'] if x['name']=='verify (TR-04, '+PROJECT+')'];check('one-exact-project-job',len(selected)==1);job=selected[0]
  check('fixed-job-head-run-terminal-success',job['id']==a.job==EXPECTED_JOB and job['run_id']==RUN and job['head_sha']==HEAD and job['status']=='completed' and job['conclusion']=='success')
  for n in ['Validate formalization manifest','Fresh sandboxed statement, axiom and kernel verification','Retain verification logs']:
   check('successful-required-step:'+n,sum(x['name']==n and x['conclusion']=='success' for x in job['steps'])==1)
  check('actual-ubuntu2404-GitHub-runner',job['labels']==['ubuntu-24.04'] and job['runner_name'].startswith('GitHub Actions '))
  matching=[x for x in listing['artifacts'] if x['name']=='lean-TR-04'];check('one-original-artifact-metadata',len(matching)==1 and matching[0]==art)
  archive=a.archive.read_bytes();rawbytes=a.job_log.read_bytes();raw=rawbytes.decode('utf-8')
  check('artifact-fixed-run-head-digest-size',art['id']==a.artifact and art['name']=='lean-TR-04' and not art['expired'] and art['workflow_run']['id']==RUN and art['workflow_run']['head_sha']==HEAD and art['digest']=='sha256:'+sha(archive) and art['size_in_bytes']==len(archive))
  if a.job_log_gz:check('raw-gzip-original-byte-identity',gzip.decompress(a.job_log_gz.read_bytes())==rawbytes)
  merges=re.findall(r'fetch[^\n]*\+([0-9a-f]{40}):refs/remotes/pull/370/merge',raw);check('one-actual-executed-merge-fetch',len(merges)==1);merge=merges[0]
  summaries=re.findall(r'HEAD is now at ([0-9a-f]+) Merge ([0-9a-f]{40}) into ([0-9a-f]{40})',raw)
  check('actual-checkout-head-base-not-live-PR-guess',len(summaries)==1 and merge.startswith(summaries[0][0]) and summaries[0][1:]==(HEAD,BASE) and 'git checkout --progress --force refs/remotes/pull/370/merge' in raw and re.search(r'git log -1 --format=%H\n[^\n]* '+merge+r'\n',raw) is not None)
  check('executed-merge-exact-parents',git('show','-s','--format=%P',merge).decode().split()==[BASE,HEAD])
  for marker in ['SHA256 digest of uploaded artifact zip is '+sha(archive),f'Artifact lean-TR-04.zip successfully finalized. Artifact ID {a.artifact}',f'Final size is {len(archive)} bytes. Artifact ID is {a.artifact}',f'/actions/runs/{RUN}/artifacts/{a.artifact}']:
   check('actual-original-upload:'+marker,marker in raw)
  members={}
  with zipfile.ZipFile(io.BytesIO(archive)) as z:
   check('original-ZIP-CRC-integrity',z.testzip() is None)
   for i in z.infolist():
    q=pathlib.PurePosixPath(i.filename)
    check('safe-unique-ordinary-ZIP-member:'+i.filename,not i.is_dir() and not q.is_absolute() and '..' not in q.parts and '\\' not in i.filename and i.filename not in members and (i.external_attr>>16)&0o170000!=0o120000 and not i.flag_bits&1)
    members[i.filename]=z.read(i)
  results=[q for q in members if q.endswith('/result.json')];check('one-actual-harness-result',len(results)==1);prefix=results[0].removesuffix('result.json');result=decode(members[results[0]])
  expected_logs=['comparator','comparator-controls','dependencies','kernel-controls','leancert-build','leancert-proof-trust','mathlib-cache','negative-native','negative-sorry','sandbox','user-service']
  expected_members={prefix+'result.json'}|{prefix+n+'.log' for n in expected_logs}|{'bootstrap/'+n+'.log' for n in ['elan','landrun-build','comparator-build']}
  check('exact15-original-artifact-members',set(members)==expected_members and len(members)==15)
  log=lambda n:members[prefix+n+'.log'].decode('utf-8')
  check('actual-receipt-merge-project-default-kernel-acceptance',result['repository_commit']==merge and result['project']==PROJECT and result['result']=='comparator-accepted' and result['lean_cert_proof_trust']=='kernel-checked' and result['verifier_profile']=='default' and result['semantic_review']=='not-performed-by-this-command')
  check('exact-three-theorem-config-no-definition-holes',result['config']==CONFIG and decode(blob(HEAD,PROJECT+'/comparator.json'))==CONFIG)
  frozenbytes=blob(HEAD,FREEZE);freeze=decode(frozenbytes);inputs=result['input_sha256']
  check('exact-final205-promotion-freeze-and-own-source-approval',sha(frozenbytes)==FREEZE_SHA and sha(blob(HEAD,APPROVAL))==APPROVAL_SHA and decode(blob(HEAD,APPROVAL))['outcome']=='approved' and len(freeze['inputs'])==205 and inputs==freeze['inputs'])
  proposal=decode(blob(HEAD,PROPOSAL))
  check('exact-approved-revision2-proposal',sha(blob(HEAD,PROPOSAL))==PROPOSAL_SHA and freeze['proposal']==dict(path=PROPOSAL,sha256=PROPOSAL_SHA) and proposal['revision']==2 and proposal['post_promotion_package_inputs']==inputs and proposal['requires_final_source_bound_Linux_receipt'] is True)
  before=decode(blob(CANDIDATE,DOC+'CANONICAL_PACKAGE_PREACCEPTANCE_FREEZE_2026-10-26.json'))['inputs']
  check('only-one-of205-package-inputs-changes-from-accepted-candidate',set(before)==set(inputs) and sorted(q for q in inputs if inputs[q]!=before[q])==['formalization.yaml'] and inputs['formalization.yaml']=='1302638065dbc0a3ea98b0b0730811b1b8828ddb95ac06441e400bcb11249633')
  for change in proposal['proposed_replacements']:
   b=blob(HEAD,change['destination'])
   check('exact-applied-approved-descriptive-replacement:'+change['destination'],sha(b)==change['proposed_sha256'] and b==blob(HEAD,change['proposed_path'])==blob(merge,change['destination'])==(repo/change['destination']).read_bytes())
  check('original-candidate795-auditor-and-receipt-retained-immutable',sha(blob(HEAD,DOC+'independent-linux-candidate-algebra/audit-linux.py'))=='82303ba91fbe0584d6ed4fb25890510fa31a13cb511330de5d69663b7cfabba2' and sha(blob(HEAD,DOC+'independent-linux-candidate-algebra/terminal-result.json'))=='576281c8bab2560176c60fdff3b4b4e5d638150092af15b1220213d55c0db6bf' and sha(blob(HEAD,DOC+'independent-linux-candidate-algebra/APPROVAL.json'))=='8fd5d17193709a4ad5a87367a751a9ac79a34cef4a6691fa0ee45853fe1546b9')
  check('exact205-head-and-merge-file-sets',tree(HEAD)==tree(merge)==set(inputs) and len(inputs)==205)
  check('exact190-Lean-inputs',sum(q.endswith('.lean') for q in inputs)==190)
  for q,h in inputs.items():
   b=blob(HEAD,PROJECT+'/'+q);check('all205-head-merge-current-input:'+q,sha(b)==h and blob(merge,PROJECT+'/'+q)==b and (repo/PROJECT/q).read_bytes()==b)
  lock=decode(blob(HEAD,PROJECT+'/proof-source-lock.json'))
  check('exact184copies179proofs190Lean-source-lock',len(lock['copies'])==lock['actual_copied_source_count']==184 and lock['actual_proof_source_count']==179 and lock['actual_canonical_Lean_input_count']==190 and lock['selected_exports']==NAMES and sum(x['module'].startswith('NLA.Proofs.TR04.') for x in lock['copies'])==179)
  for c in lock['copies']:
   q=c['module'].replace('.','/')+'.lean';b=blob(HEAD,c['source'])
   check('all184shared-source-copy-identities:'+q,c['source']=='lean-statements/'+q and c['destination']==PROJECT+'/'+q and sha(b)==c['source_sha256']==c['destination_sha256']==inputs[q] and b==blob(merge,c['source'])==blob(merge,c['destination'])==(repo/c['source']).read_bytes())
  original_manifest=decode(blob(HEAD,ORIGINAL_ARCHIVE));check('exact25-original-archive-manifest',freeze['preserved_original_archive']==ORIGINAL_ARCHIVE and sha(blob(HEAD,ORIGINAL_ARCHIVE))==ORIGINAL_ARCHIVE_SHA and len(original_manifest['records'])==25)
  for c in original_manifest['records']:
   archived=blob(HEAD,c['archive_path'])
   check('all25-archived-originals:'+c['original_path'],sha(archived)==c['sha256'] and archived==blob(merge,c['archive_path'])==blob(CANDIDATE,c['original_path'])==(repo/c['archive_path']).read_bytes())
   if c['original_path']!='tensor-computations/TR-04/README.md':
    check('all24-live-originals:'+c['original_path'],archived==blob(HEAD,c['original_path'])==blob(merge,c['original_path'])==(repo/c['original_path']).read_bytes())
  original_README=blob(CANDIDATE,'tensor-computations/TR-04/README.md');promoted_README=blob(HEAD,'tensor-computations/TR-04/README.md')
  check('entire-original-problem-statement-suffix-unchanged',promoted_README.split(b'## Problem statement\n',1)[1]==original_README.split(b'## Problem statement\n',1)[1])
  restored_prefix=promoted_README.split(b'## Lean verification',1)[0].replace(b'**Status:** Lean verified',b'**Status:** Solved').replace(b'**Last checked:** 2026-10-26',b'**Last checked:** 2026-09-11')
  check('original-resolution-prefix-only-status-date-changes',restored_prefix==original_README.split(b'## Lean formalization scaffold',1)[0])
  check('all217-permanent-ID-path-pairs',len(decode(blob(HEAD,'problem_ids.json')))==217 and blob(HEAD,'problem_ids.json')==blob(BASE,'problem_ids.json'))
  challenge=blob(merge,PROJECT+'/Challenge.lean').decode();solution=blob(merge,PROJECT+'/Solution.lean').decode()
  for n in NAMES[:2]:check('literal-retained-support-theorem-type:'+n,header(challenge,n)==header(solution,n))
  check('literal-full-Target-wrapper-types',header(blob(merge,PROJECT+'/FullChallenge.lean').decode(),'target')==header(blob(merge,PROJECT+'/FullSolution.lean').decode(),'target')=='theorem target : NLA.Statements.TR04.Target')
  body=lambda t:t.split('def Target : Prop :=',1)[1].split('#assert_statement',1)[0]
  check('literal-original-Target-reviewed-mirror-rfl',body(blob(merge,PROJECT+'/NLA/Statements/TR04.lean').decode())==body(blob(merge,PROJECT+'/Reviewed/TR04.lean').decode()) and 'NLA.Statements.TR04.Target=NLA.ReviewedStatements.TR04.Target := rfl' in blob(merge,PROJECT+'/Identity.lean').decode())
  # Derive actual runtime build scope, instead of assuming every input is used.
  visited=set();pending=['FullChallenge','FullSolution']
  while pending:
   n=pending.pop()
   if n in visited:continue
   q=n.replace('.','/')+'.lean'
   if q not in inputs:continue
   visited.add(n)
   for imports in re.findall(r'^import\s+(.+)$',blob(merge,PROJECT+'/'+q).decode(),re.M):pending+=imports.split('--')[0].split()
  solseen=set();pending=['FullSolution']
  while pending:
   n=pending.pop()
   if n in solseen:continue
   q=n.replace('.','/')+'.lean'
   if q not in inputs:continue
   solseen.add(n)
   for imports in re.findall(r'^import\s+(.+)$',blob(merge,PROJECT+'/'+q).decode(),re.M):pending+=imports.split('--')[0].split()
  check('actual-solution-import-closure-has-no-Challenge',not({'Challenge','FullChallenge'}&solseen))
  for q,h in PINNED_TOOL_FILES.items():check('fixed-reviewed-harness-workflow-source:'+q,sha(blob(HEAD,q))==h and blob(HEAD,q)==blob(merge,q)==blob(BASE,q))
  tool=result['tool_receipt'];tool_lock=decode(blob(merge,'tools/lean/source-lock.json'))
  check('pinned-actual-Forsythe-tool-receipt',result['source_lock_sha256']==tool['source_lock_sha256']==sha(blob(merge,'tools/lean/source-lock.json')) and tool['forsythe_commit']==tool_lock['commit']=='8d1b0c0545a77b40245e84705aa7d273e6c81e62' and tool['profile']=='default')
  check('actual-complete-tool-binary-env-digests',set(tool['executables'])=={'.tools/comparator/.lake/build/bin/comparator','.tools/lean4export/.lake/build/bin/lean4export','.tools/bin/landrun'} and all(re.fullmatch('[0-9a-f]{64}',v) for v in list(tool['executables'].values())+[tool['env_sha256']]))
  check('actual-official-Linux-compiler-and-Go',tool['lean_toolchain']=='leanprover/lean4:v4.33.1' and tool['lean_version']=='Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)' and tool['lean_version'] in raw and tool['platform'].startswith('Linux-') and tool['go_version']=='go version go1.27.1 linux/amd64')
  harness=blob(merge,'tools/lean/harness.py').decode();parsed=ast.parse(harness);validated=next(n for n in parsed.body if isinstance(n,ast.FunctionDef) and n.name=='validated_tools');verify=next(n for n in parsed.body if isinstance(n,ast.FunctionDef) and n.name=='verify');validated_text=ast.get_source_segment(harness,validated)
  check('actual-harness-revalidates-binaries-and-environment',any(isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='validated_tools' for n in ast.walk(verify)) and all(x in validated_text for x in ['for name, expected in receipt["executables"].items():','if digest(file) != expected:','modified checker executable:','if digest(tool_dir / ".tools/env.sh") != receipt["env_sha256"]:']))
  consumer=proof_consumer();check('actual-generated-theorem-kind-kernel-consumer',sha(consumer.encode())==result['lean_cert_proof_trust_source_sha256'] and all('#assert_proof_constant '+n in consumer and '#assert_trust kernel '+n in consumer for n in NAMES))
  trust=log('leancert-proof-trust');comp=log('comparator')
  check('actual-kernel-consumer-ran-isolated','ProofTrustAudit.lean' in trust and 'RestrictAddressFamilies=~AF_UNIX' in trust and trust.rstrip().endswith('EXIT_STATUS=0'))
  ax=axiom_records(trust)
  check('exact-per-export-transitive-axioms',[n for n,_ in ax]==NAMES and all(xs==EXPECTED_AXIOMS[n] for n,xs in ax),expected=EXPECTED_AXIOMS,observed=ax)
  exports=[x for x in comp.splitlines() if x.startswith('Exporting #[')]
  check('actual-Comparator-three-exact-export-names',len(exports)==2 and exports[0].endswith(' from FullChallenge') and exports[1].endswith(' from FullSolution') and all(selected_exports(x)==NAMES for x in exports))
  for marker in ['Building FullChallenge','Building FullSolution','Running Lean default kernel on solution.','Lean default kernel accepts the solution','Your solution is okay!','scripts/strict_landrun.py','systemd-run --user']:
   check('actual-default-kernel-Comparator:'+marker,marker in comp)
  for n in sorted(visited):check('actual-imported-source-built-or-replayed:'+n,re.search(r'(?:Built|Replayed) '+re.escape(n)+r'\b',comp) is not None)
  runtime={q.removesuffix('.lean').replace('/','.') for q in inputs if q.endswith('.lean')}
  compiled={n for n in runtime if re.search(r'(?:Built|Replayed) '+re.escape(n)+r'\b',comp)}
  check('exact187-actual-imported-modules179proofs-not190',len(visited)==len(compiled)==187 and sum(n.startswith('NLA.Proofs.TR04.') for n in compiled)==179 and sorted(runtime-compiled)==['Check','Identity','Reviewed.TR04'])
  for marker in ['RETURN honest_with_inductives_and_quotients: accepted','RETURN invalid_raw_proof: rejected:','(kernel) declaration type mismatch','RETURN quotient_postcheck_mismatch: rejected:','Quotient post-check rejects the solution','PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:
   check('actual-raw-kernel-control:'+marker,marker in log('kernel-controls'))
  for n,code,marker in [('simple_match',0,'Your solution is okay!'),('simple_mismatch',1,"Challenge and solution constant kind don't match: 'comm'"),('simple_axiom_issue',1,"Illegal axiom detected: 'helper'"),('simple_kind_mismatch',1,"Illegal axiom detected: 'helper'"),('type_mismatch',1,"Challenge and solution theorem statement do not match: 'checked'")]:
   check('actual-Comparator-regression:'+n,f'PASS {n}: exit {code}, expected {code}; required phase: {marker}' in log('comparator-controls'))
  check('actual-five-Comparator-regressions-complete','PASS: all five Comparator regressions' in log('comparator-controls'))
  check('actual-two-sandbox-modes','MODE build: exit=0' in log('sandbox') and 'MODE export: exit=0' in log('sandbox'))
  for marker in ['outside .lake write-open: denied','outside .lake truncate: denied','outside .lake read-only truncate-open: denied','symlink from .lake to outside write: denied','outside .lake creation: denied','user namespace: private','pid namespace: private','mnt namespace: private','net namespace: private','ipc namespace: private','uts namespace: private','host parent: absent from private /proc','host parent signal lookup: denied','host loopback listener: unreachable','AF_UNIX socket creation: denied','effective capabilities: none','no_new_privs: set','nested namespace write attempt: rejected']:
   check('actual-both-mode-isolation:'+marker,log('sandbox').count('PASS '+marker)==2)
  for marker in ['PASS build .lake write: allowed','PASS export .lake write-open: denied','PASS export .lake truncate: denied','Outer and export fixture contents unchanged; only designated build fixture written.']:
   check('actual-build-only-write-policy:'+marker,marker in log('sandbox'))
  for marker in ['unknown option','unexpected --rw','unexpected --rwx','relative --rwx']:
   check('actual-negative-sandbox-option:'+marker,'NEGATIVE '+marker+': exit=2' in log('sandbox'))
  check('actual-sorry-rejection',"Illegal axiom detected: 'sorryAx'" in log('negative-sorry') and log('negative-sorry').rstrip().endswith('EXIT_STATUS=1'))
  check('actual-native-rejection',"Illegal axiom detected: 'checked._native.native_decide.ax_1_1'" in log('negative-native') and log('negative-native').rstrip().endswith('EXIT_STATUS=1'))
  pins={x['name']:(x['url'],x['rev']) for x in decode(blob(merge,PROJECT+'/lake-manifest.json'))['packages']}
  check('all10-dependency-pins-original-shared-identity',len(pins)==10 and pins=={x['name']:(x['url'],x['rev']) for x in decode(blob(merge,'lean-statements/lake-manifest.json'))['packages']})
  for n,(url,rev) in pins.items():check('actual-dependency-checkout:'+n,re.fullmatch('[0-9a-f]{40}',rev) and "checking out revision '"+rev+"'" in log('dependencies'))
  check('actual-LeanCert-build-and-user-service','lake build LeanCert.Tactic.Verification' in log('leancert-build') and 'RestrictAddressFamilies=~AF_UNIX' in log('user-service'))
  check('actual-checker-and-landrun-bootstrap','lake build lean4export comparator' in members['bootstrap/comparator-build.log'].decode() and 'go build -mod=readonly -buildvcs=false' in members['bootstrap/landrun-build.log'].decode())
  probe_path='docs/lean/verification/2026-09-12/source/forsythe/reproduction/checks/sandbox_probe.py';probe=blob(merge,probe_path);probe_pin=next(x for x in tool_lock['files'] if x['destination']=='reproduction/checks/sandbox_probe.py')
  check('locked-original-and-generated-CI-sandbox-probe',sha(probe)==probe_pin['sha256'] and len(probe)==probe_pin['bytes'] and sha(probe_source(probe.decode()).encode())==tool['ci_sandbox_probe_sha256'])
  rawlines=[re.sub(r'^\ufeff?\d{4}-\d\d-\d\dT[^ ]+Z ','',x) for x in raw.splitlines()]
  command_positions={}
  for q,b in members.items():
   if q.endswith('.log'):
    command=b.decode().splitlines()[0]
    check('actual-log-command-header:'+q,command.startswith('$ '))
    marker='Running '+command[2:]
    positions=[i for i,line in enumerate(rawlines) if line==marker]
    check('unique-actual-command-boundary:'+q,len(positions)==1 and marker not in command_positions)
    command_positions[marker]=positions[0]
  for q,b in sorted(members.items()):
   if not q.endswith('.log'):continue
   lines=b.decode().splitlines();status=1 if q.endswith(('negative-native.log','negative-sorry.log')) else 0
   check('every-actual-log-exit:'+q,lines[-1]=='EXIT_STATUS='+str(status))
   check('every-command-present-in-raw-job:'+q,lines[0].startswith('$ ') and 'Running '+lines[0][2:] in rawlines)
   start=command_positions['Running '+lines[0][2:]]+1
   end=min([i for i in command_positions.values() if i>=start]+[len(rawlines)])
   pos=start
   for line in lines[1:]:
    if line and not line.startswith('EXIT_STATUS='):pos=rawlines.index(line,pos,end)+1
   check('every-artifact-body-line-bound-to-raw-job:'+q,True)
  check('raw-job-complete-harness-success','PASS: fresh Comparator run and all controls. Evidence:' in raw)
  check('all-provided-evidence-bytes-unchanged',all(sha(pathlib.Path(q).read_bytes())==h for q,h in evidence_hashes.items()))
  check('all205-current-package-bytes-still-frozen',all(sha((repo/PROJECT/q).read_bytes())==h for q,h in inputs.items()))
  details=dict(run=RUN,job=a.job,artifact=a.artifact,head=HEAD,base=BASE,executed_merge=merge,archive_sha256=sha(archive),archive_bytes=len(archive),raw_log_sha256=sha(rawbytes),raw_log_bytes=len(rawbytes),result_sha256=sha(members[results[0]]),consumer_sha256=sha(consumer.encode()),package_inputs=205,Lean_inputs=190,copied_sources=184,proof_sources=179,selected_theorems=NAMES,expected_axioms=EXPECTED_AXIOMS,actual_import_build_scope=sorted(visited),actual_build_markers=sorted(compiled),input_bound_without_Linux_build_marker=sorted(runtime-compiled),artifact_member_sha256={q:sha(b) for q,b in sorted(members.items())},tool_receipt=tool)
 except Exception as exc:error=str(exc)
 finally:
  if reader is not None:
   reader.stdin.close();reader.wait()
 report=dict(reviewer='/root/recover_algebra',scope='Independent read-only integrity audit of actual final-promotion GitHub Linux/Comparator bytes and approved descriptive delta; own authored mathematical prerequisites excluded from independent mathematical source scope',passed=error is None and all(x['passed'] for x in checks),error=error,check_count=len(checks),checks=checks,driver_sha256=sha(pathlib.Path(__file__).read_bytes()),evidence_file_sha256=evidence_hashes,limitations=['No network, checkout, extraction, Lean, Comparator or new Linux execution was performed by this auditor.','Actual executed source comes from raw checkout plus immutable Git parents, not a mutable current PR merge SHA.','All190 Lean inputs are hash-bound; only actual import-closure build markers are claimed compiled in this job. Separate local fresh audits cover unused helper files.','Semantic proof fidelity and my authored prerequisites rely on separately bound independent source/kernel reviews; receipt integrity review does not claim independent authorship of those proofs.'],**details)
 with output.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:report[k] for k in ['passed','error','check_count','driver_sha256']},indent=2));return 0 if report['passed'] else 1

if __name__=='__main__':raise SystemExit(main())
