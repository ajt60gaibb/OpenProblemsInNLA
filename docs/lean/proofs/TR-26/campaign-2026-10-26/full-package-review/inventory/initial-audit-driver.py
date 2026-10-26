#!/usr/bin/env python3
"""Independent immutable full TR26 package audit; no canonical source edits."""
import argparse,hashlib,io,json,re,subprocess,tarfile,functools
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--extract',type=Path);p.add_argument('--reviews-root',type=Path,default=Path(__file__).resolve().parents[2]);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
C='f0fc0691c3496822e330894de60a9d6e94b7890a';S='ecc597cb68b65b473aecce9ac635e27d35c09694';I='4692336f0e1a50d5e261bba68277875da30fba51';H='6c607ab14af2b8b2b8075f0b3f1798e037c10899';B='5487945e5a72abd952b0c89915915de8cc9b3e65';P='tensor-computations/TR-26/lean/';D='docs/lean/proofs/TR-26/campaign-2026-10-26/'
git=lambda *v:subprocess.check_output(['git',*v],cwd=a.repo);sha=lambda b:hashlib.sha256(b).hexdigest()
@functools.lru_cache(None)
def read(c,q):return git('show',c+':'+q)
archive=git('archive',C,P);t=tarfile.open(fileobj=io.BytesIO(archive));data={x.name.removeprefix(P):t.extractfile(x).read() for x in t.getmembers() if x.isfile()};checks=[]
def check(n,b,**d):checks.append(dict(name=n,passed=bool(b),**d))
lock=json.loads(data['PACKAGE_LOCK.json']);sm=json.loads(data['SOURCE_MAP.json']);names=['NLA.Proofs.TR26.nonisotropic_degree','NLA.Proofs.TR26.isotropic_degree','NLA.Proofs.TR26.target']
check('857locked-inputs-plus-lock',len(data)==858 and len(lock['files'])==857 and set(data)-set(lock['files'])=={'PACKAGE_LOCK.json'} and lock['proof_source_ref']==S)
for q,x in lock['files'].items():check('locked-hash-size:'+q,q in data and sha(data[q])==x['sha256'] and len(data[q])==x['bytes'])
shared=[x for x in sm['copies'] if x['path'].startswith(('NLA/','Reviewed/')) and x['path'].endswith('.lean')]
check('80actual-shared-copies-278all-copy-mappings',len(shared)==80 and len(sm['copies'])==278 and sm['proof_source_ref']==S)
for x in sm['copies']:check('all278exact-copy-mappings:'+x['path'],x['source_ref'] in {I,S} and data[x['path']]==read(x['source_ref'],x['source_path']) and sha(data[x['path']])==x['sha256'] and len(data[x['path']])==x['bytes'])
for x in shared:check('same80approved-fullsources:'+x['path'],x['source_ref']==S and data[x['path']]==read(C,x['source_path'])==read(S,x['source_path']))
runtime={q:b for q,b in data.items() if q.endswith('.lean') and (q.startswith(('NLA/','Reviewed/')) or '/' not in q)}
check('84runtime-sources-no-archival-glob-leak',len(runtime)==84 and set(runtime)-{x['path'] for x in shared}=={'Challenge.lean','Solution.lean','Identity.lean','EndpointAudit.lean'} and not any(q.startswith('reviews/') for q in runtime))
cfg=json.loads(data['comparator.json']);check('exact3theorems-no-definition-holes-standard3',cfg==dict(challenge_module='Challenge',solution_module='Solution',theorem_names=names,definition_names=[],permitted_axioms=['propext','Classical.choice','Quot.sound']))
meta=json.loads(data['formalization.yaml']);check('truthful-full-candidate-not-promoted',meta['status']['phase']=='full-target-candidate' and meta['status']['whole_problem_verified'] is False and meta['status']['canonical_status']=='Solved' and [x['declaration'] for x in meta['status']['main_results']]==names)
check('reference-byte-exact-preapproved-three-holes',data['Challenge.lean']==read(S,D+'preproof/Challenge.lean') and len(re.findall(r'\bsorry\b',data['Challenge.lean'].decode()))==3)
check('solution-imports-actual-MainTarget-never-Challenge','import NLA.Proofs.TR26.MainTarget' in data['Solution.lean'].decode() and 'import Challenge' not in data['Solution.lean'].decode())
check('all3actual-kind-kernel-exact-frozen-audit',all('#package_theorem '+n in data['EndpointAudit.lean'].decode() and '#assert_trust kernel '+n in data['EndpointAudit.lean'].decode() for n in names) and all(x in data['EndpointAudit.lean'].decode() for x in ['NLA.ReviewedStatements.TR26.HasReducedDegree','NLA.ReviewedStatements.TR26.NonisotropicClosure','NLA.ReviewedStatements.TR26.IsotropicImage','example : NLA.ReviewedStatements.TR26.Target := NLA.Proofs.TR26.target','Target = NLA.ReviewedStatements.TR26.Target := rfl']))
check('identity-only-not-a-Target-proof','not a proof of the full Target' in data['Identity.lean'].decode())
pre=json.loads(read(S,D+'preproof/INPUT_LOCK.json'))
for x in pre['reviewed_inputs']:check('original24-preserved:'+x['path'],read(C,x['path'])==read(B,x['path'])==read(C,D+'preproof/frozen/'+x['path']) and sha(read(C,x['path']))==x['sha256'])
check('217permanentIDs-paths',read(C,'problem_ids.json')==read(S,'problem_ids.json')==read(B,'problem_ids.json') and len(json.loads(read(C,'problem_ids.json')))==217)
check('original-canonical-README-Solved-untouched',read(C,'tensor-computations/TR-26/README.md')==read(B,'tensor-computations/TR-26/README.md')==data['sources/ORIGINAL.md'] and b'**Status:** Solved' in data['sources/ORIGINAL.md'])
for ext in ['md','tex','pdf']:check('manuscript-original:'+ext,data['sources/TR-26.'+ext]==read(B,'references/colbrook-unclaimed-2026-09-11/manuscripts/TR-26.'+ext))
manifest=json.loads(data['lake-manifest.json']);check('all10dependency-pins-preserved',manifest['packages']==json.loads(read(S,'lean-statements/lake-manifest.json'))['packages'] and len(manifest['packages'])==10)
check('official4331-pinned',data['lean-toolchain']==b'leanprover/lean4:v4.33.1\n')
check('credit-and-acceptance-limits','Matthew J. Colbrook' in json.dumps(meta) and 'no external human endorsement' in json.dumps(meta) and 'actual Linux/Comparator' in json.dumps(meta))
review_counts={}
for filename in ['reviews/SOURCE_REVIEW_BINDINGS.json','reviews/FULL_SOURCE_REVIEW_BINDINGS.json']:
 x=json.loads(data[filename]);review_counts[filename]=len(x['files'])
 for z in x['files']:check('review-binding:'+z['path'],z['path'] in data and sha(data[z['path']])==z['sha256'] and len(data[z['path']])==z['bytes'])
 for who in ['inventory','verification']:
  prefix='reviews/full-target-review/'+who+'/' if 'FULL_' in filename else 'reviews/isotropic/'+who+'/'
  local=a.reviews_root/('tr26-full-target-review' if 'FULL_' in filename else 'tr26-isotropic-review')/who
  for z in x['files']:
   if z['path'].startswith(prefix):
    q=local/z['path'].removeprefix(prefix);check('independent-review-verbatim:'+z['path'],q.is_file() and q.read_bytes()==data[z['path']])
for q,b in data.items():
 prefix='reviews/partial-package-6c607ab/'
 if q.startswith(prefix):
  old=q.removeprefix(prefix);old=old.removesuffix('.txt') if old.endswith('.lean.txt') else old
  check('historical-partial-metadata-verbatim:'+q,b==read(H,P+old))
check('historical-scopes-explicitly-separated','historical scope statements' in data['README.md'].decode() and 'isotropic-only' in data['README.md'].decode())
# Historical report hashes remain unchanged; their partial scope is not promoted.
for who in ['inventory','verification']:
 q='reviews/isotropic/'+who+'/REVIEW.md';check('old-isotropic-review-remains-exact:'+who,data[q]==read(H,P+q))
if a.extract:
 a.extract.mkdir(parents=True,exist_ok=False)
 for q,b in data.items():f=a.extract/q;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
r=dict(reviewer='/root/inventory',scope='Independent full candidate canonical package audit. Mathematical full-source review is separate; no actual Linux/CI/exporter/raw-kernel claim.',commit=C,proof_source_commit=S,authored_proof_sources=[],package_files=len(data),locked_input_count=len(lock['files']),runtime_Lean_source_count=len(runtime),all_Lean_files_including_archives=sum(q.endswith('.lean') for q in data),shared_copy_count=len(shared),all_copy_mappings=len(sm['copies']),review_binding_counts=review_counts,whole_problem_verified=False,canonical_status='Solved',actual_exports=names,checks=checks,check_count=len(checks),passed=all(x['passed'] for x in checks),findings=[x for x in checks if not x['passed']],all_package_sha256={q:sha(b) for q,b in data.items()},runtime_sha256={q:sha(b) for q,b in runtime.items()},auditor_sha256=sha(Path(__file__).read_bytes()))
(a.output/'PACKAGE_REVIEW.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k] for k in ['passed','check_count','findings','locked_input_count','runtime_Lean_source_count','all_Lean_files_including_archives','review_binding_counts']},indent=2));raise SystemExit(0 if r['passed'] else 1)
