#!/usr/bin/env python3
"""Independent exact-commit RE06 transcript/Frobenius support source/preservation audit."""
import argparse,hashlib,io,json,re,subprocess,tarfile
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--commit',default='a271ab2e3ef066187c4c7c26ca10c3f40bcf2ba9');p.add_argument('--reuse-repo',type=Path,default=Path('/Users/ajt253/Documents/OpenProblemsInNLA/campaign-workspaces/tr04'));a=p.parse_args();r=a.repo.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
C='a271ab2e3ef066187c4c7c26ca10c3f40bcf2ba9';AUTH='bb0dd13e3321bb35af762936a75c2c3a8a8363c6';PACKET='729832293829263c2e51dbd6ecc9788ad68b7792';BASE='099805ef1ce7347d373e47cccc3b2d7cf580a99e';D='docs/lean/proofs/RE-06/campaign-2026-10-26/';P=D+'preproof/';sha=lambda b:hashlib.sha256(b).hexdigest();checks=[];details={}
def git(*v,repo=r):return subprocess.check_output(['git',*v],cwd=repo)
def read(c,q,repo=r):return git('show',c+':'+q,repo=repo)
def ck(n,v,**x):
 checks.append(dict(name=n,passed=bool(v),**x))
 if not v:raise AssertionError(n)
def audit():
 ck('exact-immutable-source-checkpoint',git('rev-parse',a.commit+'^{commit}').decode().strip()==C)
 ck('implementation-authorized-before-source',subprocess.run(['git','merge-base','--is-ancestor',AUTH,C],cwd=r).returncode==0 and subprocess.run(['git','merge-base','--is-ancestor',PACKET,AUTH],cwd=r).returncode==0)
 auth=json.loads(read(C,D+'IMPLEMENTATION_AUTHORIZATION.json'));ck('real-explicit-implementation-authorization',auth['implementation_authorized'] is True and auth['frozen_packet_commit']==PACKET and auth['canonical_status']=='Solved' and auth['whole_problem_verified'] is False)
 for q,h in auth['reviewed_packet_hashes'].items():ck('exact-authorized-preproof-packet-byte:'+q,sha(read(C,P+q))==h and read(C,P+q)==read(PACKET,P+q))
 ck('two-new-independent-non-author-preproof-approvals',{x['reviewer'] for x in auth['independent_non_author_approvals']}=={'/root/inventory','/root/verification'})
 for x in auth['independent_non_author_approvals']:
  ck('real-preproof-approval-report:'+x['reviewer'],sha(read(C,D+x['report']))==x['sha256'] and sha(read(C,D+x['approval']))==x['approval_sha256'])
 allpacket=git('ls-tree','-r','--name-only',PACKET,P).decode().splitlines();ck('103-frozen-preproof-files-retained',len(allpacket)==103)
 for q in allpacket:ck('frozen-preproof-byte:'+q,read(C,q)==read(PACKET,q))
 inputs=json.loads(read(C,P+'INPUT_LOCK.json'));ck('49-published-inputs-locked',len(inputs['files'])==49 and inputs['published_base']==BASE)
 for e in inputs['files']:
  b=read(C,e['path']);ck('published-input:'+e['path'],sha(b)==e['sha256'] and len(b)==e['bytes'] and b==read(BASE,e['path'])==read(C,P+'originals/'+e['path']))
 reuse=json.loads(read(C,P+'REUSE_LOCK.json'));ck('9-reviewed-reuse-provenance-inputs',len(reuse['files'])==9 and reuse['source_commit']=='653b8f1641415f4160811648ff3e23889ba2e136')
 for e in reuse['files']:
  b=read(C,P+'supplementary-reuse/'+e['path']);ck('locked-reuse-original:'+e['path'],sha(b)==e['sha256'] and len(b)==e['bytes'] and b==read(reuse['source_commit'],e['path'],repo=a.reuse_repo))
 ids=read(C,'problem_ids.json');ck('217-ID-registry-byte-exact',len(json.loads(ids))==217 and ids==read(BASE,'problem_ids.json') and json.loads(ids)['RE-06']=='randomized-and-low-rank-approximation/RE-06/README.md')
 freeze=json.loads(read(C,D+'transcript-author/SOURCE_FREEZE.json'));ck('exact-three-file27-support-freeze-no-public-promotion',sha(read(C,D+'transcript-author/SOURCE_FREEZE.json'))=='eff7205186985ea505618b0e1b23233096f94f2feeb01dca0f31de5194e75029' and len(freeze['proof_files'])==3 and freeze['support_theorems']==27 and not freeze['unconditional_public_success_proved'] and not freeze['full_Target_proved'] and not freeze['independent_approval'] and not freeze['Linux_CI'] and not freeze['Comparator'])
 for e in freeze['proof_files']:
  b=read(C,e['path']);ck('all3-frozen-source-bytes:'+e['path'],sha(b)==e['sha256'] and len(b)==e['bytes'])
  ck('no-proof-holes-new-axioms-or-unsafe-evaluation:'+e['path'],re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|run_tac)\b',b.decode()) is None)
 ck('two-proof-local-conservative-definitions',freeze['conservative_helper_definitions']==['NLA.Proofs.RE06.sketchWarmIndex','NLA.Proofs.RE06.sketchRepair'])
 report_bytes=read(C,D+'transcript-author/fresh-replay/RESULT.json');report=json.loads(report_bytes);ck('author11replay-is-truthfully-author-only',report['passed'] and len(report['records'])==11 and all(x['passed'] for x in report['records']) and 'AUTHOR ONLY' in report['scope'] and sha(report_bytes)==freeze['fresh_result_sha256'])
 diagnostic_paths=git('ls-tree','-r','--name-only',C,D+'transcript-author/attempts/negative-alias-inference/').decode().splitlines();ck('author-alias-control-diagnostic-preserved',len(diagnostic_paths)>=3 and any(x.endswith('DIAGNOSTIC.md') for x in diagnostic_paths))
 manifest=json.loads(read(C,'lean-statements/lake-manifest.json'));pins={x['name']:x['rev'] for x in manifest['packages']};ck('exact10dependency-pins',len(pins)==10 and pins['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474' and pins['leancert']=='621a43d7cf21f87872392a01e874f2f1dbddc926')
 ck('canonical-README-remains-unchanged-Solved',b'**Status:** Solved' in read(C,inputs['canonical_readme']))
 models=['NLA.Computation.SVDMachine','NLA.Computation.NonadaptiveMatrixQuery','NLA.Statements.Infrastructure','NLA.Statements.RE06','Reviewed.RE06'];proofs=['NLA.Proofs.RE06.Transcript','NLA.Proofs.RE06.Frobenius','NLA.Proofs.RE06.TranscriptAudit']
 source_dir=out/'immutable-source';source_dir.mkdir(exist_ok=True)
 source_hashes={}
 for m in models+proofs:
  q='lean-statements/'+m.replace('.','/')+'.lean';b=read(C,q);f=source_dir/(m.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b);source_hashes[q]=sha(b)
 for q in ['Challenge.lean','CONTRACT.md','READINESS.md','INPUT_LOCK.json','REUSE_LOCK.json','PACKET_LOCK.json']:(out/q).write_bytes(read(C,P+q))
 for q in ['SOURCE_FREEZE.json','AUTHOR_REPORT.md']:(out/q).write_bytes(read(C,D+'transcript-author/'+q))
 return dict(commit=C,source_freeze_sha256=sha(read(C,D+'transcript-author/SOURCE_FREEZE.json')),authorization_commit=AUTH,packet_commit=PACKET,published_base=BASE,proof_source_files=freeze['proof_files'],compiled_input_sha256=source_hashes,pins=pins,support_theorems=freeze['theorems'],conservative_helper_definitions=freeze['conservative_helper_definitions'],whole_problem_verified=False,canonical_status='Solved')
error=None
try:details=audit()
except Exception as e:error=str(e)
j=dict(reviewer='/root/inventory',authored_RE06_proof_sources=[],scope='Independent transcript/Frobenius support source/preservation review; conditional branch success only, no unconditional success/fullTarget/Linux claim.',passed=error is None,check_count=len(checks),checks=checks,error=error,driver_sha256=sha(Path(__file__).read_bytes()),**details)
(out/'SOURCE_REVIEW.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps({k:j[k] for k in ['passed','error','check_count']}));raise SystemExit(0 if j['passed'] else 1)
