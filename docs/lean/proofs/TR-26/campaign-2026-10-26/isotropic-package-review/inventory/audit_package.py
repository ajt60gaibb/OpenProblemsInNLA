#!/usr/bin/env python3
"""Immutable TR26 isotropic-only canonical package audit and optional snapshot."""
import argparse,hashlib,json,re,subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--extract',type=Path)
a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
C='6c607ab14af2b8b2b8075f0b3f1798e037c10899';S='4692336f0e1a50d5e261bba68277875da30fba51';B='5487945e5a72abd952b0c89915915de8cc9b3e65'
P='tensor-computations/TR-26/lean/';D='docs/lean/proofs/TR-26/campaign-2026-10-26/'
git=lambda *v:subprocess.check_output(['git',*v],cwd=a.repo);read=lambda c,q:git('show',c+':'+q);sha=lambda b:hashlib.sha256(b).hexdigest()
paths=git('ls-tree','-r','--name-only',C,P).decode().splitlines();data={q.removeprefix(P):read(C,q) for q in paths};checks=[]
def check(n,b,**d):checks.append(dict(name=n,passed=bool(b),**d))
lock=json.loads(data['PACKAGE_LOCK.json']);sm=json.loads(data['SOURCE_MAP.json'])
check('353locked-inputs-plus-lock-itself',len(data)==354 and len(lock['files'])==353 and set(data)-set(lock['files'])=={'PACKAGE_LOCK.json'} and lock['proof_source_ref']==S)
for q,x in lock['files'].items():check('all353locked-hash-and-size:'+q,q in data and sha(data[q])==x['sha256'] and len(data[q])==x['bytes'])
check('exact36shared-source-map',len([x for x in sm['copies'] if x['path'].startswith(('NLA/','Reviewed/')) and x['path'].endswith('.lean')])==36 and len(sm['copies'])==117 and sm['proof_source_ref']==S)
for x in sm['copies']:
 check('all36exact-reviewed-source-copies:'+x['path'],x['source_ref']==S and data[x['path']]==read(S,x['source_path'])==read(C,x['source_path']) and sha(data[x['path']])==x['sha256'] and len(data[x['path']])==x['bytes'])
runtime={q:b for q,b in data.items() if q.endswith('.lean') and (q.startswith(('NLA/','Reviewed/')) or '/' not in q)}
check('exact40runtime-Lean-sources',len(runtime)==40 and set(runtime)-{x['path'] for x in sm['copies']}=={'Challenge.lean','Solution.lean','Identity.lean','EndpointAudit.lean'})
check('archive-Lean-files-outside-runtime-globs',len([q for q in data if q.endswith('.lean')])==76 and not any(q.startswith('reviews/') for q in runtime))
cfg=json.loads(data['comparator.json']);name='NLA.Proofs.TR26.isotropic_degree'
check('only-one-literal-actual-isotropic-export',cfg==dict(challenge_module='Challenge',solution_module='Solution',theorem_names=[name],definition_names=[],permitted_axioms=['propext','Classical.choice','Quot.sound']))
meta=json.loads(data['formalization.yaml']);check('metadata-no-whole-target-or-nonisotropic-promotion',meta['status']['whole_problem_verified'] is False and meta['status']['phase']=='support-only' and meta['status']['canonical_status']=='Solved' and [x['declaration'] for x in meta['status']['main_results']]==[name] and 'remain unproved' in meta['project']['description'])
check('solution-never-imports-reference','import NLA.Proofs.TR26.IsotropicDegree' in data['Solution.lean'].decode() and 'import Challenge' not in data['Solution.lean'].decode())
check('actual-exact-endpoint-kind-kernel-and-absence-guards',all(t in data['EndpointAudit.lean'].decode() for t in ['#package_theorem '+name,'#assert_trust kernel '+name,'#package_absent NLA.Proofs.TR26.nonisotropic_degree','#package_absent NLA.Proofs.TR26.target']))
check('frozen-live-identity-not-labelled-proof','Target = NLA.ReviewedStatements.TR26.Target := rfl' in data['Identity.lean'].decode() and 'not a proof of the full Target' in data['Identity.lean'].decode())
check('reference-one-intentional-hole-only',len(re.findall(r'\bsorry\b',data['Challenge.lean'].decode()))==1 and 'isotropic_degree' in data['Challenge.lean'].decode() and 'nonisotropic_degree' not in data['Challenge.lean'].decode())
pre=json.loads(read(S,D+'preproof/INPUT_LOCK.json'))
for x in pre['reviewed_inputs']:
 b=read(B,x['path']);check('all24originals-preserved:'+x['path'],b==read(C,x['path'])==read(C,D+'preproof/frozen/'+x['path']) and sha(b)==x['sha256'])
check('registry217IDs-paths-retained',read(C,'problem_ids.json')==read(S,'problem_ids.json')==read(B,'problem_ids.json') and len(json.loads(read(C,'problem_ids.json')))==217)
check('canonical-original-page-stays-Solved',read(C,'tensor-computations/TR-26/README.md')==read(B,'tensor-computations/TR-26/README.md') and data['sources/ORIGINAL.md']==read(B,'tensor-computations/TR-26/README.md') and b'**Status:** Solved' in data['sources/ORIGINAL.md'])
for ext in ['md','tex','pdf']:check('complete-manuscript-original:'+ext,data['sources/TR-26.'+ext]==read(B,'references/colbrook-unclaimed-2026-09-11/manuscripts/TR-26.'+ext))
manifest=json.loads(data['lake-manifest.json']);shared=json.loads(read(S,'lean-statements/lake-manifest.json'))
check('all10dependency-records-pins-preserved',manifest['packages']==shared['packages'] and len(manifest['packages'])==10)
check('pinned-official-compiler',data['lean-toolchain']==b'leanprover/lean4:v4.33.1\n')
check('metadata-credit-and-review-limitations','Matthew J. Colbrook' in json.dumps(meta) and 'no external human endorsement' in json.dumps(meta))
review_snapshots=[]
for folder,source_folder in [('reviews/isotropic/inventory/','tr26-isotropic-review/inventory/'),('reviews/isotropic/verification/','tr26-isotropic-review/verification/')]:
 local=Path(__file__).resolve().parents[2]/source_folder
 if local.exists():
  for q,b in data.items():
   if q.startswith(folder):
    f=local/q.removeprefix(folder)
    check('copied-independent-review-verbatim:'+q,f.is_file() and f.read_bytes()==b)
    review_snapshots.append(q)
if a.extract:
 a.extract.mkdir(parents=True,exist_ok=False)
 for q,b in data.items():f=a.extract/q;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
r=dict(reviewer='/root/inventory',scope='Independent immutable canonical partial-package audit only; fresh runtime/Comparator-library comparison remains separate from actual Linux CI.',commit=C,proof_source_commit=S,authored_proof_sources=[],package_files=354,locked_input_count=353,runtime_Lean_source_count=40,all_Lean_files_including_archives=76,shared_copy_count=36,whole_problem_verified=False,canonical_status='Solved',actual_selected_exports=[name],checks=checks,check_count=len(checks),passed=all(x['passed'] for x in checks),findings=[x for x in checks if not x['passed']],all354_package_sha256={q:sha(b) for q,b in data.items()},runtime40_sha256={q:sha(b) for q,b in runtime.items()},auditor_sha256=sha(Path(__file__).read_bytes()))
(a.output/'PACKAGE_REVIEW.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k] for k in ['passed','check_count','findings','locked_input_count','runtime_Lean_source_count']},indent=2))
raise SystemExit(0 if r['passed'] else 1)
