#!/usr/bin/env python3
"""Prepare an explicitly candidate TR-26 full package from immutable sources."""
import argparse,hashlib,json,re,shutil,subprocess
from pathlib import Path
SOURCE_REF='ecc597cb68b65b473aecce9ac635e27d35c09694'
PARTIAL_REF='6c607ab14af2b8b2b8075f0b3f1798e037c10899'
CAMP='docs/lean/proofs/TR-26/campaign-2026-10-26'
PKG='tensor-computations/TR-26/lean'
AXIOMS=['propext','Classical.choice','Quot.sound']
EXPORTS=['NLA.Proofs.TR26.nonisotropic_degree','NLA.Proofs.TR26.isotropic_degree','NLA.Proofs.TR26.target']
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--full-reviews-root',type=Path);a=ap.parse_args()
 out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
 def git(path,ref=SOURCE_REF):return subprocess.check_output(['git','show',f'{ref}:{path}'],cwd=a.repo)
 def paths(prefix,ref=SOURCE_REF):return subprocess.check_output(['git','ls-tree','-r','--name-only',ref,'--',prefix],cwd=a.repo,text=True).splitlines()
 def write(p,data):
  dest=out/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data if isinstance(data,bytes) else data.encode())
 def js(p,d):write(p,json.dumps(d,indent=2,ensure_ascii=False)+'\n')
 sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 for p in paths(PKG+'/',PARTIAL_REF):write(p.removeprefix(PKG+'/'),git(p,PARTIAL_REF))
 oldmap=json.loads((out/'SOURCE_MAP.json').read_text());copies=[x for x in oldmap['copies'] if not x['path'].endswith('.lean') or x['path'].startswith('reviews/')]
 for p in ['README.md','formalization.yaml','comparator.json','Solution.lean','Challenge.lean','EndpointAudit.lean','Identity.lean','PACKAGE_LOCK.json','SOURCE_MAP.json']:
  suffix='.txt' if p.endswith('.lean') else ''
  write('reviews/partial-package-6c607ab/'+p+suffix,(out/p).read_bytes())
 freeze=json.loads(git(CAMP+'/FULL_TARGET_SOURCE_FREEZE.json'))
 for row in freeze['proof_inputs']+freeze['shared_inputs']:
  p=row['path'];target=p.removeprefix('lean-statements/');data=git(p)
  assert hashlib.sha256(data).hexdigest()==row['sha256'];write(target,data)
  copies.append({'path':target,'source_path':p,'source_ref':SOURCE_REF,'sha256':row['sha256'],'bytes':len(data)})
 write('Challenge.lean',git(CAMP+'/preproof/Challenge.lean'))
 write('Solution.lean','''import NLA.Proofs.TR26.MainTarget

/-! Both literal degree endpoints and the unchanged full Target. Acceptance
of this candidate package is recorded separately in source-bound reviews
and actual Linux/Comparator receipts. -/
set_option leancert.trust "kernel"
''')
 audit=git(CAMP+'/full-target-author/FullTargetAudit.lean.txt').decode().replace('import NLA.Proofs.TR26.MainTarget','import Solution').replace('#full_target_theorem','#package_theorem').replace('full target audit requires','package requires')
 write('EndpointAudit.lean',audit)
 write('controls/ChallengeTrustRejection.lean.txt','import Challenge\n'+''.join('#assert_trust kernel '+x+'\n' for x in EXPORTS))
 write('controls/DefinitionKindRejection.lean.txt','''import EndpointAudit
def FakeFullTarget : NLA.Statements.TR26.Target := NLA.Proofs.TR26.target
#package_theorem FakeFullTarget
''')
 write('controls/CustomAxiomRejection.lean.txt','''import EndpointAudit
axiom PackageOracle : NLA.Statements.TR26.Target
theorem OracleFullTarget : NLA.Statements.TR26.Target := PackageOracle
#assert_trust kernel OracleFullTarget
''')
 for p in [CAMP+'/FULL_TARGET_SOURCE_FREEZE.json',CAMP+'/FULL_TARGET_SOURCE.md']+paths(CAMP+'/full-target-author/'):
  target='reviews/full-target-source/'+p.removeprefix(CAMP+'/')
  if target.endswith('.lean'):target+='.txt'
  write(target,git(p))
  data=git(p);copies.append({'path':target,'source_path':p,'source_ref':SOURCE_REF,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)})
 js('comparator.json',{'challenge_module':'Challenge','solution_module':'Solution','theorem_names':EXPORTS,'definition_names':[],'permitted_axioms':AXIOMS})
 manifest=json.loads((out/'lake-manifest.json').read_text());manifest['name']='NLATR26';js('lake-manifest.json',manifest)
 write('lakefile.toml',(out/'lakefile.toml').read_text().replace('NLATR26Isotropic','NLATR26'))
 metadata=json.loads((out/'formalization.yaml').read_text())
 metadata['project']['name']='TR-26: exact reduced degrees of both discriminant parts'
 metadata['project']['description']='Both unchanged all-order reduced-degree endpoints and literal original Target, including d=2; candidate canonical package awaiting source-bound acceptance.'
 metadata['project']['authors']=['OpenAI Codex AI agents /root, /root/proof_route and /root/ie22_sampling (formal implementation); final independent non-author reviews are separately bound below']
 metadata['sources'][1]['location']='Both parts of Theorem 1; fixed unweighted and bilinear model'
 metadata['automation']['methods'][0]['prompting_notes']='Two independent exact pre-proof approvals preceded implementation; preserve all originals and both exact endpoints.'
 metadata['status'].update({'phase':'full-target-candidate','scope':'Both exact reduced-degree endpoints and literal full Target for every d>=2, retaining full incidence ideal, all projective representatives, raw isotropic image and nonisotropic closure.','whole_problem_verified':False,'canonical_status':'Solved','main_results':[{'declaration':name,'file':'NLA/Proofs/TR26/'+file+'.lean','sorry_count':0,'axioms':AXIOMS,'comparator_config':'comparator.json','verification_status':'Author kernel acceptance only; independent full-source/package reviews and actual Linux/Comparator acceptance are separately required.'} for name,file in zip(EXPORTS,['NonisotropicDegree','IsotropicDegree','MainTarget'])]})
 metadata['fidelity']['divergences']='No mathematical divergence is intended: the frozen original Target and both exact degree endpoints are consumed literally. Candidate author builds do not imply final package or Linux/Comparator acceptance.'
 metadata['review']={'status':'Two independent pre-proof approvals and two earlier isotropic endpoint source approvals; full-source/package and Linux acceptance pending','reviewers':['/root/inventory','/root/verification'],'notes':'Earlier isotropic-only reviews remain verbatim under reviews/isotropic. They do not approve the later nonisotropic endpoint or full Target. Full author source checkpoint '+SOURCE_REF+' is bound separately.'}
 if a.full_reviews_root:
  bindings=[];omitted=[]
  for reviewer in ['inventory','verification']:
   src=a.full_reviews_root/reviewer
   assert (src/'REVIEW.md').is_file(),src
   for artifact in sorted(src.rglob('*')):
    if artifact.is_file() and artifact.suffix in ['.pyc','.pyo','.olean','.ilean']:
     omitted.append({'path':'reviews/full-target-review/'+reviewer+'/'+artifact.relative_to(src).as_posix(),'sha256':sha(artifact),'bytes':artifact.stat().st_size,'reason':'Regenerable compiler output, not a proof or review source input.'})
   dst=out/'reviews/full-target-review'/reviewer;shutil.copytree(src,dst,ignore=shutil.ignore_patterns('__pycache__','*.pyc','*.pyo','*.olean','*.ilean'))
   for p in sorted(dst.rglob('*')):
    if p.is_file():
     assert p.suffix not in ['.olean','.ilean'];bindings.append({'path':p.relative_to(out).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size})
  js('reviews/FULL_SOURCE_REVIEW_BINDINGS.json',{'proof_source_ref':SOURCE_REF,'scope':'Two independent exact full-source reviews; canonical-package and Linux acceptance are separate gates.','files':bindings,'omitted_regenerable_artifacts':omitted})
  metadata['review']['status']='Two independent full-source AI-agent reviews retained; canonical package and actual Linux acceptance separate'
  metadata['review']['notes']='Both full-source review packets are retained verbatim under reviews/full-target-review and bound by FULL_SOURCE_REVIEW_BINDINGS.json. Source checkpoint '+SOURCE_REF+'. No package or Linux acceptance is implied by these reports.'
  for rec in metadata['status']['main_results']:rec['verification_status']='Author and two independent full-source LeanCert kernel audits; canonical package and actual Linux/Comparator receipt separate.'
 js('formalization.yaml',metadata)
 js('SOURCE_MAP.json',{'proof_source_ref':SOURCE_REF,'prior_partial_package_ref':PARTIAL_REF,'scope':'Both exact degree endpoints and full Target; source review/package review/Linux acceptance are distinct.','copies':copies})
 write('README.md','''# TR-26 exact full Target candidate

This package supplies actual proofs of both preapproved endpoints and the unchanged full Target: for every d≥2, `NonisotropicClosure d` has reduced degree `6*(d-1)` and the raw `IsotropicImage d` has reduced degree `2*d`. The original unweighted Veronese curve, bilinear pairings, independent complex symmetric-matrix coordinates and full incidence vanishing ideal/Jacobian are retained. Both projective charts, the point at infinity, matrix-kernel directions and d=2 are included.

`Challenge.lean` is exactly the independently approved pre-proof reference with three intentional holes. Solution imports no Challenge. Comparator selects all three genuine theorems, with no replaceable definition holes and only the standard three foundational axioms. `EndpointAudit.lean` checks theorem kinds, kernel trust, exact frozen-reviewed endpoint consumers and the original/frozen Target identity. `Identity.lean` alone remains only an equality check.

All 77 proof modules and three shared statement/reference modules are byte-exact copies from source checkpoint `ecc597cb68b65b473aecce9ac635e27d35c09694`. SOURCE_MAP records copies and hashes. Complete originals, manuscript, pre-proof approvals and earlier independent isotropic-only source reviews are preserved. Earlier partial metadata is retained under reviews/partial-package-6c607ab; those historical scope statements describe that earlier package. Later full-source and canonical-package reviews and Linux receipts have their own exact source bindings.

This is a full Target candidate. TR-26 remains **Solved** until required independent reviews and actual Linux/Comparator verification support promotion. Author or local source replay is not an isolated Linux or raw-kernel receipt. Mathematical source credit remains with Matthew J. Colbrook; AI agents implemented the formalization and reviews. No external human endorsement or new licence grant is claimed.

For a fresh local replay, run `python3 reproduce.py --lean /absolute/path/to/pinned/lean --packages /absolute/path/to/pinned/packages --output /new/empty/output/path`. This checks 84 runtime sources with fresh own objects and three actual rejection controls; the first control rejects all three reference holes. Pins: Lean 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and LeanCert 621a43d7cf21f87872392a01e874f2f1dbddc926. The repository's unchanged tools/lean/verify.sh separately supplies genuine Linux isolation, theorem-kind/axiom checks, Comparator and raw-kernel replay.
''')
 sourcepaths={x['path'] for x in copies if x['path'].endswith('.lean') and not x['path'].startswith('reviews/')}
 assert len(sourcepaths)==80
 graph={p:[dep for line in (out/p).read_text().splitlines() if line.startswith('import ') for m in line.split()[1:] if (dep:=m.replace('.','/')+'.lean') in sourcepaths] for p in sourcepaths}
 ordered=[];active=set()
 def visit(p):
  if p in ordered:return
  assert p not in active,p
  active.add(p)
  for dep in graph[p]:visit(dep)
  active.remove(p);ordered.append(p)
 for p in sorted(sourcepaths):visit(p)
 replay=(out/'reproduce.py').read_text().replace('one TR-26 isotropic endpoint','the exact TR-26 full Target').replace('Local source replay of the literal isotropic endpoint only','Local source replay of both literal endpoints and full Target; no final package or Linux claim').replace('nla-tr26-isotropic-local-replay-','nla-tr26-full-local-replay-')
 start=replay.index("        files = ['NLA/Statements/Infrastructure.lean'");end=replay.index('\n        with tempfile.TemporaryDirectory',start)
 replay=replay[:start]+'        files = '+repr(ordered+['Challenge.lean','Solution.lean','EndpointAudit.lean','Identity.lean'])+replay[end:]
 write('reproduce.py',replay)
 files={p.relative_to(out).as_posix():{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(out.rglob('*')) if p.is_file() and p.name!='PACKAGE_LOCK.json'}
 # Include any historical nested PACKAGE_LOCK under its archived path too.
 historical=out/'reviews/partial-package-6c607ab/PACKAGE_LOCK.json';files[historical.relative_to(out).as_posix()]={'sha256':sha(historical),'bytes':historical.stat().st_size}
 js('PACKAGE_LOCK.json',{'proof_source_ref':SOURCE_REF,'scope':'Both exact endpoints and full Target candidate; final acceptance separately bound.','files':files})
 print(json.dumps({'locked_inputs':len(files),'shared_Lean_copies':len(sourcepaths),'runtime_Lean_inputs':len(ordered)+4,'comparator_exports':EXPORTS,'proof_source_ref':SOURCE_REF}))
if __name__=='__main__':main()
