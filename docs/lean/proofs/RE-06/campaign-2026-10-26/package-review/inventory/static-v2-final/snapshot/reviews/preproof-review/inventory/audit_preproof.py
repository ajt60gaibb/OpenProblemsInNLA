#!/usr/bin/env python3
"""Immutable non-author RE06 pre-proof input/header/model-preservation audit."""
import argparse,functools,hashlib,io,json,re,subprocess,tarfile
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--reuse-repo',type=Path,required=True);p.add_argument('--external-packet',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--extract',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
C='729832293829263c2e51dbd6ecc9788ad68b7792';B='099805ef1ce7347d373e47cccc3b2d7cf580a99e';R='653b8f1641415f4160811648ff3e23889ba2e136';D='docs/lean/proofs/RE-06/campaign-2026-10-26/preproof/';sha=lambda b:hashlib.sha256(b).hexdigest()
@functools.lru_cache(None)
def read(c,q,reuse=False):return subprocess.check_output(['git','show',c+':'+q],cwd=a.reuse_repo if reuse else a.repo)
t=tarfile.open(fileobj=io.BytesIO(subprocess.check_output(['git','archive',C,D],cwd=a.repo)));data={x.name.removeprefix(D):t.extractfile(x).read() for x in t if x.isfile()};checks=[]
def check(n,v):checks.append(dict(name=n,passed=bool(v)));assert v,n
for q,h in [('PACKET_LOCK.json','f318ade71c4e97a2952052ee94c76ca254e558bc0f9bbc15b72d90a738106bc9'),('INPUT_LOCK.json','fda0f85d913233b3c62b707b46bf0edd2fca9ba8ba34a618b57d6bc7bb4e222a'),('CONTRACT.md','5e98b497102cc1626825ed4fe11016417f406467e5ace86b6858d13d47b6ba9c'),('Challenge.lean','21f59e23c4c4b0168eb031de49b0fe8c31c72179713f1479c895a8020bc7d1a8')]:check('frozen-author-packet:'+q,sha(data[q])==h)
packet=json.loads(data['PACKET_LOCK.json']);lock=json.loads(data['INPUT_LOCK.json']);reuse=json.loads(data['REUSE_LOCK.json']);exports=json.loads(data['EXPORTS.json'])['exports'];check('102locked-plus-lock103',len(data)==103 and len(packet['files'])==102 and set(data)=={x['path'] for x in packet['files']}|{'PACKET_LOCK.json'})
for x in packet['files']:
 b=data[x['path']];check('all102packet-inputs:'+x['path'],sha(b)==x['sha256'] and len(b)==x['bytes'])
for q,b in data.items():check('external-frozen-packet-identical:'+q,(a.external_packet/q).read_bytes()==b)
check('published49inputs',lock['published_base']==B and len(lock['files'])==49)
for x in lock['files']:
 b=data['originals/'+x['path']];check('all49published-originals:'+x['path'],b==read(B,x['path'])==read(C,x['path']) and sha(b)==x['sha256'] and len(b)==x['bytes'])
check('all217permanent-IDs',read(C,'problem_ids.json')==read(B,'problem_ids.json') and len(json.loads(read(C,'problem_ids.json')))==217 and json.loads(read(C,'problem_ids.json'))['RE-06']=='randomized-and-low-rank-approximation/RE-06/README.md')
check('9separate-reuse-inputs',reuse['source_commit']==R and len(reuse['files'])==9)
for x in reuse['files']:
 b=data['supplementary-reuse/'+x['path']];check('actual-reuse9-sourcehash:'+x['path'],b==read(R,x['path'],True) and sha(b)==x['sha256'] and len(b)==x['bytes']);check('actual-reuse9-gitblob:'+x['path'],subprocess.check_output(['git','rev-parse',R+':'+x['path']],cwd=a.reuse_repo).decode().strip()==x['git_blob'])
check('SVD-model-byteidentical-reuse-published',data['supplementary-reuse/lean-statements/NLA/Computation/SVDMachine.lean']==data['originals/lean-statements/NLA/Computation/SVDMachine.lean'])
challenge=data['Challenge.lean'].decode();check('exact6orderedexports',[x['name'] for x in exports]==['svd_total','query_bound','successful','original_claim','explicit_claim','target'])
for x in exports:
 pattern=r'theorem\s+'+x['name']+r'\s*'+re.escape(x['binders']).replace(r'\ ',r'\s*')+r'\s*:\s*'+re.escape(x['type'])+r'\s*:=\s*by\s+sorry'
 check('literal-approved-header:'+x['name'],re.search(pattern,challenge) is not None)
check('exact6holes-and-kernelassertions',len(re.findall(r'\bsorry\b',challenge))==6 and all('#assert_trust kernel '+x['name'] in challenge for x in exports))
check('no-RE06-proof-source-created',not subprocess.check_output(['git','ls-tree','-r','--name-only',C,'lean-statements/NLA/Proofs/RE06'],cwd=a.repo).strip())
check('not-already-authorized',packet['implementation_authorized'] is False and packet['independent_preproof_approvals']==0)
model=data['originals/lean-statements/NLA/Computation/NonadaptiveMatrixQuery.lean'].decode();statement=data['originals/lean-statements/NLA/Statements/RE06.lean'].decode()
check('plan-no-A-family-or-answer-argument','makePlan (n m : ℕ) (ε : ℝ) (ω : ℕ → ℝ)' in model)
check('postprocess-no-A-or-oracle-argument','postprocess {n m : ℕ} (F : Family n m)\n    (P : Plan n) (responses : List (Fin n → ℝ))' in model)
check('actual-stream-probability-and-success','Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)' in model and 'GaussianLaw {ω | frobenius A (run F A ε ω) ≤ (3 + ε) * optimum A F}' in model and '(99 / 100 : ENNReal)' in model)
check('unconditional-query-all-streams','∀ ω : ℕ → ℝ' in model and 'QueryBound n m ε 4000000 0' in statement)
check('closed-target-three-required-conjuncts','def Target : Prop := SVDTotal ∧ OriginalClaim ∧ ExplicitClaim' in statement)
check('fullrectangular-affirmative-SVDTotal','∀ (a b : ℕ) (B : Matrix (Fin a) (Fin b) ℝ)' in model and 'ValidSVDResult B (exactSVD B)' in model)
check('canonicalstatus-stillSolved',b'**Status:** Solved' in read(C,lock['canonical_readme']))
a.extract.mkdir(parents=True,exist_ok=False)
for q,b in data.items():f=a.extract/q;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
r=dict(reviewer='/root/inventory',phase='independent pre-proof input/header/source preservation only',authored_RE06_proofs=[],commit=C,published_base=B,reuse_source=R,packet_files=103,originals=49,reuse_files=9,IDs_paths=217,hashes={q:sha(b) for q,b in data.items()},exports=exports,checks=checks,check_count=len(checks),passed=all(x['passed'] for x in checks),auditor_sha256=sha(Path(__file__).read_bytes()))
(a.output/'INPUT_REVIEW.json').write_text(json.dumps(r,indent=2)+'\n');print('PASS',len(checks),'checks;103packet49original9reuse217IDs6headers')
