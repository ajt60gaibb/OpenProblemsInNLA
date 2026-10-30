#!/usr/bin/env python3
"""Independent exact-commit RE06 Gaussian foundation/residual source/preservation audit."""
import argparse,hashlib,io,json,re,subprocess,tarfile
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--commit',default='d043142e4d7dd45c8a8aee5d10f989f44c356cb9');p.add_argument('--reuse-repo',type=Path,default=Path('/Users/ajt253/Documents/OpenProblemsInNLA/campaign-workspaces/tr04'));a=p.parse_args();r=a.repo.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
C='d043142e4d7dd45c8a8aee5d10f989f44c356cb9';AUTH='bb0dd13e3321bb35af762936a75c2c3a8a8363c6';PACKET='729832293829263c2e51dbd6ecc9788ad68b7792';BASE='099805ef1ce7347d373e47cccc3b2d7cf580a99e';D='docs/lean/proofs/RE-06/campaign-2026-10-26/';P=D+'preproof/';sha=lambda b:hashlib.sha256(b).hexdigest();checks=[];details={}
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
 freeze_bytes=read(C,D+'gaussian-author/SOURCE_FREEZE.json');freeze=json.loads(freeze_bytes);ck('exact16-Gaussian-source-freeze',sha(freeze_bytes)=='25df9cc498f942893db019705aed0457fc78bceeedab893d5d31f4a68481c3d5' and len(freeze['files'])==16 and freeze['new_frozen_modules']==16 and not freeze['unconditional_public_success_proved'] and not freeze['full_Target_proved'] and not freeze['independent_approval'] and not freeze['Linux_CI'] and not freeze['Comparator'])
 binding_commit='21b660e25e313fe6f1d43b57d1338522bf50ea38';binding_bytes=read(binding_commit,D+'gaussian-author/CLOSED_SOURCE_BINDING.json');binding=json.loads(binding_bytes)
 ck('complete23-input-binding-separate-descendant-metadata',binding['closed_source_commit']==C and len(binding['files'])==23 and not binding['new_Gaussian_source_bytes_changed'] and binding['initial_module_commit_did_not_yet_track_PseudoInverseCore'] and not git('ls-tree','--name-only',C,D+'gaussian-author/CLOSED_SOURCE_BINDING.json').strip() and subprocess.run(['git','merge-base','--is-ancestor',C,binding_commit],cwd=r).returncode==0)
 ck('historical-sixteen-only-snapshot-really-lacked-tracked-PseudoInverseCore',not git('ls-tree','--name-only',binding['initial_sixteen_module_commit'],'lean-statements/NLA/Proofs/RE06/PseudoInverseCore.lean').strip())
 for q,e in freeze['files'].items():
  b=read(C,q);ck('all16-frozen-Gaussian-bytes:'+q,sha(b)==e['sha256'] and len(b)==e['bytes'] and b==read(binding['initial_sixteen_module_commit'],q))
  ck('no-Gaussian-proof-holes-new-axioms-unsafe-evaluation:'+q,re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|run_tac)\b',b.decode()) is None)
 for e in binding['files']:
  b=read(C,e['path']);ck('all23-closed-source-inputs:'+e['path'],sha(b)==e['sha256'] and len(b)==e['bytes'])
 imports={};visited=set();order=[]
 def walk(m):
  if m in visited:return
  visited.add(m);q='lean-statements/'+m.replace('.','/')+'.lean';b=read(C,q).decode();im=[v for line in b.splitlines() if line.startswith('import ') for v in line.split()[1:] if v.startswith(('NLA.','Reviewed.'))];imports[m]=im
  for dep in im:walk(dep)
  order.append(m)
 for q in freeze['files']:walk(q.removeprefix('lean-statements/').removesuffix('.lean').replace('/','.'))
 ck('actual-23-module-import-closure-complete',len(order)==23 and {'lean-statements/'+m.replace('.','/')+'.lean' for m in order}=={e['path'] for e in binding['files']})
 for q in ['NLA.Statements.Infrastructure','NLA.Statements.RE06','Reviewed.RE06']:walk(q)
 ck('own-replay26sources-includes-original-boundary',len(order)==26)
 (out/'CLOSED_SOURCE_BINDING.json').write_bytes(binding_bytes)
 for stem in ['re06-gaussian-foundations','re06-gaussian-residual']:
  for name in ['README.md','AUTHOR_KERNEL_RECEIPT.json']:(out/(stem+'-'+name)).write_bytes(read(C,D+'gaussian-author/'+stem+'/'+name))
 manifest=json.loads(read(C,'lean-statements/lake-manifest.json'));pins={x['name']:x['rev'] for x in manifest['packages']};ck('exact10dependency-pins',len(pins)==10 and pins['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474' and pins['leancert']=='621a43d7cf21f87872392a01e874f2f1dbddc926')
 ck('canonical-README-remains-unchanged-Solved',b'**Status:** Solved' in read(C,inputs['canonical_readme']))
 models=order;proofs=[]
 source_dir=out/'immutable-source';source_dir.mkdir(exist_ok=True)
 source_hashes={}
 for m in models+proofs:
  q='lean-statements/'+m.replace('.','/')+'.lean';b=read(C,q);f=source_dir/(m.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b);source_hashes[q]=sha(b)
 for q in ['Challenge.lean','CONTRACT.md','READINESS.md','INPUT_LOCK.json','REUSE_LOCK.json','PACKET_LOCK.json']:(out/q).write_bytes(read(C,P+q))
 for q in ['SOURCE_FREEZE.json']:(out/q).write_bytes(read(C,D+'gaussian-author/'+q))
 return dict(commit=C,source_freeze_sha256=sha(read(C,D+'gaussian-author/SOURCE_FREEZE.json')),authorization_commit=AUTH,packet_commit=PACKET,published_base=BASE,proof_source_files=freeze['files'],binding_commit=binding_commit,closed_binding_sha256=sha(binding_bytes),compile_modules=order,import_graph=imports,compiled_input_sha256=source_hashes,pins=pins,Gaussian_frozen_module_count=16,actual_Gaussian_closure_count=23,own_replay_closure_count=26,whole_problem_verified=False,canonical_status='Solved')
error=None
try:details=audit()
except Exception as e:error=str(e)
j=dict(reviewer='/root/inventory',authored_RE06_proof_sources=[],scope='Independent actual Gaussian foundations/residual source review; exact closed d043 snapshot; no unconditional success/fullTarget/Linux claim.',passed=error is None,check_count=len(checks),checks=checks,error=error,driver_sha256=sha(Path(__file__).read_bytes()),**details)
(out/'SOURCE_REVIEW.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps({k:j[k] for k in ['passed','error','check_count']}));raise SystemExit(0 if j['passed'] else 1)
