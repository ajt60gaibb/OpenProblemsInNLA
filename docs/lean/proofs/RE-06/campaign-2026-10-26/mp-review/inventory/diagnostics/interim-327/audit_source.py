#!/usr/bin/env python3
"""Independent exact-commit RE06 actual pseudoinverse/fullrank/global-measurability support source/preservation audit."""
import argparse,hashlib,io,json,re,subprocess,tarfile
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--commit',default='b8eb4d7d07dd4a682c81ba48f43ef93314fbc20b');p.add_argument('--reuse-repo',type=Path,default=Path('/Users/ajt253/Documents/OpenProblemsInNLA/campaign-workspaces/tr04'));a=p.parse_args();r=a.repo.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
C='b8eb4d7d07dd4a682c81ba48f43ef93314fbc20b';AUTH='bb0dd13e3321bb35af762936a75c2c3a8a8363c6';PACKET='729832293829263c2e51dbd6ecc9788ad68b7792';BASE='099805ef1ce7347d373e47cccc3b2d7cf580a99e';D='docs/lean/proofs/RE-06/campaign-2026-10-26/';P=D+'preproof/';sha=lambda b:hashlib.sha256(b).hexdigest();checks=[];details={}
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
 freezes={};expected={'pseudoinverse-author':'36d5668471158268fc367e8f544c0811b86697cfd507d11396331aabe2967914','fullrank-author':'63b662c1e1f00f3f85fa14adc61c93704bf866826568f33f30b853a7010978ac','global-measurable-author':'316d68f325c38f30cc7020da7ea1b803f8f8e8f2c5af6efb1cf53d90bc9e0b27'}
 for stem,h in expected.items():
  b=read(C,D+stem+'/SOURCE_FREEZE.json');f=json.loads(b);freezes[stem]=f
  ck('exact-phase-source-freeze:'+stem,sha(b)==h and f['canonical_status']=='Solved' and f['whole_problem_verified'] is False and f['authorization_commit']==AUTH)
  dest=out/stem;dest.mkdir(exist_ok=True);(dest/'SOURCE_FREEZE.json').write_bytes(b);(dest/'AUTHOR_REPORT.md').write_bytes(read(C,D+stem+'/AUTHOR_REPORT.md'))
  for e in f['files']:
   b=read(C,e['path']);ck('phase-source-input:'+stem+':'+e['path'],sha(b)==e['sha256'] and len(b)==e['bytes'])
 ck('95actual-support-theorems-in-three-phases',sum(f['new_actual_support_theorems'] for f in freezes.values())==95 and [f['new_mathematical_modules'] for f in freezes.values()]==[13,2,3])
 for e in freezes['pseudoinverse-author']['files']:ck('pseudoinverse26-tracked-d043-source-bytes-retained:'+e['path'],read(C,e['path'])==read('d043142e4d7dd45c8a8aee5d10f989f44c356cb9',e['path']))
 for parent,child in [('pseudoinverse-author','fullrank-author'),('fullrank-author','global-measurable-author')]:
  pm={e['path']:(e['sha256'],e['bytes'],e['module']) for e in freezes[parent]['files']};cm={e['path']:(e['sha256'],e['bytes'],e['module']) for e in freezes[child]['files']}
  ck('phase-parent-frozen-source-bindings-preserved:'+child,all(cm.get(q)==v for q,v in pm.items()) and freezes[child]['parent_source_freeze_sha256']==expected[parent])
 freeze=freezes['global-measurable-author'];ck('complete33tracked-source-inputs',len(freeze['files'])==33 and not freeze['new_Matrix_measurable_or_Borel_instances'])
 imports={};visited=set();order=[]
 def walk(m):
  if m in visited:return
  visited.add(m);q='lean-statements/'+m.replace('.','/')+'.lean';text=read(C,q).decode();im=[dep for line in text.splitlines() if line.startswith('import ') for dep in line.split()[1:] if dep.startswith(('NLA.','Reviewed.'))];imports[m]=im
  for dep in im:walk(dep)
  order.append(m)
 for e in freeze['files']:walk(e['module'])
 ck('exact-complete33-import-source-set',len(order)==33 and {'lean-statements/'+m.replace('.','/')+'.lean' for m in order}=={e['path'] for e in freeze['files']})
 changed_math=[]
 for stem,f in freezes.items():
  new=[e['module'] for e in f['files'] if e['new_in_chunk'] and not e['module'].endswith('Audit')];changed_math+=new;ck('declared-new-mathematical-source-count:'+stem,len(new)==f['new_mathematical_modules'])
  for e in f['files']:
   if e['new_in_chunk']:ck('no-new-math-holes-axioms-unsafe:'+e['path'],re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|run_tac)\b',read(C,e['path']).decode()) is None)
 ck('eighteen-new-math-modules-unique',len(changed_math)==len(set(changed_math))==18)
 manifest=json.loads(read(C,'lean-statements/lake-manifest.json'));pins={x['name']:x['rev'] for x in manifest['packages']};ck('exact10dependency-pins',len(pins)==10 and pins['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474' and pins['leancert']=='621a43d7cf21f87872392a01e874f2f1dbddc926')
 ck('canonical-README-remains-unchanged-Solved',b'**Status:** Solved' in read(C,inputs['canonical_readme']))
 models=order;proofs=[]
 source_dir=out/'immutable-source';source_dir.mkdir(exist_ok=True)
 source_hashes={}
 for m in models+proofs:
  q='lean-statements/'+m.replace('.','/')+'.lean';b=read(C,q);f=source_dir/(m.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b);source_hashes[q]=sha(b)
 for q in ['Challenge.lean','CONTRACT.md','READINESS.md','INPUT_LOCK.json','REUSE_LOCK.json','PACKET_LOCK.json']:(out/q).write_bytes(read(C,P+q))

 return dict(commit=C,source_freeze_sha256=expected,authorization_commit=AUTH,packet_commit=PACKET,published_base=BASE,proof_source_files=freeze['files'],compile_modules=order,import_graph=imports,new_math_modules=changed_math,compiled_input_sha256=source_hashes,pins=pins,actual_support_theorems=95,closed_source_count=33,whole_problem_verified=False,canonical_status='Solved')
error=None
try:details=audit()
except Exception as e:error=str(e)
j=dict(reviewer='/root/inventory',authored_RE06_proof_sources=[],scope='Independent actual MP/fullrank/global-measurable support source review; no rectangular inverse-Wishart or success/fullTarget/Linux claim.',passed=error is None,check_count=len(checks),checks=checks,error=error,driver_sha256=sha(Path(__file__).read_bytes()),**details)
(out/'SOURCE_REVIEW.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps({k:j[k] for k in ['passed','error','check_count']}));raise SystemExit(0 if j['passed'] else 1)
