#!/usr/bin/env python3
"""Independent immutable TR26 status/metadata delta audit. No source edits or Lean run."""
import argparse,hashlib,io,json,re,subprocess,tarfile
from pathlib import Path
from collections import Counter
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True);p.add_argument('--commit',required=True);p.add_argument('--output',type=Path,required=True)
a=p.parse_args();root=a.repo.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
BASE='fa85c05acc70bbaa05bb3346fb43b57b1546af67';SOURCE='ecc597cb68b65b473aecce9ac635e27d35c09694'
PRJ='tensor-computations/TR-26/lean';DOC='docs/lean/proofs/TR-26';CAMP=DOC+'/campaign-2026-10-26'
NAMES=['NLA.Proofs.TR26.nonisotropic_degree','NLA.Proofs.TR26.isotropic_degree','NLA.Proofs.TR26.target']
checks=[];details={};sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*v):return subprocess.check_output(['git',*v],cwd=root)
def read(c,q):return git('show',c+':'+q)
def archive(c,paths):
 b=git('archive','--format=tar',c,*paths)
 with tarfile.open(fileobj=io.BytesIO(b)) as t:return {m.name:t.extractfile(m).read() for m in t.getmembers() if m.isfile()}
def ck(n,v,**x):
 checks.append(dict(name=n,passed=bool(v),**x))
 if not v:raise AssertionError(n)
def audit():
 c=git('rev-parse',a.commit+'^{commit}').decode().strip();ids=read(c,'problem_ids.json');registry=json.loads(ids)
 ck('217-permanent-IDs-and-canonical-paths-byte-identical',len(registry)==217 and ids==read(BASE,'problem_ids.json'))
 paths=[PRJ,CAMP,'tensor-computations/TR-26/README.md','tensor-computations/TR-26/ORIGINAL.md',DOC+'/LINUX_CI_RECEIPT.md',DOC+'/FULL_TARGET_PACKAGE.md','README.md','CATALOG.md','tensor-computations/README.md','docs/lean/statements/inventory.json','docs/lean/statements/COVERAGE.md']+list(registry.values())
 new=archive(c,paths);old=archive(BASE,[PRJ,'tensor-computations/TR-26/README.md','docs/lean/statements/inventory.json'])
 package={q.removeprefix(PRJ+'/'):b for q,b in new.items() if q.startswith(PRJ+'/')}
 oldpackage={q.removeprefix(PRJ+'/'):b for q,b in old.items() if q.startswith(PRJ+'/')}
 ck('exact857-package-input-set-preserved',len(package)==857 and set(package)==set(oldpackage))
 changed=sorted(q for q in package if package[q]!=oldpackage[q]);ck('only-three-descriptive-package-files-changed',changed==['PACKAGE_LOCK.json','README.md','formalization.yaml'])
 lock=json.loads(package['PACKAGE_LOCK.json']);ck('856-lock-entries-exact-package-minus-self',len(lock['files'])==856 and set(lock['files'])==set(package)-{'PACKAGE_LOCK.json'} and lock['proof_source_ref']==SOURCE)
 for q,b in package.items():
  if q in lock['files']:ck('current-lock-content:'+q,lock['files'][q]=={'sha256':sha(b),'bytes':len(b)})
  if q not in changed:ck('accepted-fa85-input-preserved:'+q,b==oldpackage[q])
 runtime=[q for q in package if q.endswith('.lean') and not q.startswith('reviews/')]
 exe=runtime+['controls/ChallengeTrustRejection.lean.txt','controls/CustomAxiomRejection.lean.txt','controls/DefinitionKindRejection.lean.txt','comparator.json','lake-manifest.json','lakefile.toml','lean-toolchain','reproduce.py']
 ck('all84-runtime-and92-executable-pin-inputs-byte-unchanged',len(runtime)==84 and len(exe)==92 and all(package[q]==oldpackage[q] for q in exe))
 for q in exe:ck('executable-pin-identity:'+q,package[q]==oldpackage[q])
 cfg=json.loads(package['comparator.json']);ck('all-three-actual-exports-no-definition-allowances',cfg['theorem_names']==NAMES and cfg['definition_names']==[] and set(cfg['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'})
 checkpoint=json.loads(read(SOURCE,CAMP+'/FULL_TARGET_SOURCE_FREEZE.json'));src=archive(SOURCE,[x['path'] for x in checkpoint['proof_inputs']+checkpoint['shared_inputs']])
 ck('source-scope77proof-plus3shared',len(checkpoint['proof_inputs'])==77 and len(checkpoint['shared_inputs'])==3)
 for e in checkpoint['proof_inputs']+checkpoint['shared_inputs']:
  q=e['path'].removeprefix('lean-statements/');b=src[e['path']]
  ck('exact-approved-ECC-mathematical-source:'+q,package[q]==b and sha(b)==e['sha256'] and len(b)==e['bytes'])
 frozen=json.loads(new[CAMP+'/preproof/INPUT_LOCK.json']);ck('24-original-inputs-retained',len(frozen['reviewed_inputs'])==24)
 for e in frozen['reviewed_inputs']:
  q=e['path'];base=read(BASE,q)
  ck('original-input-base-lock:'+q,sha(base)==e['sha256'] and len(base)==e['bytes'])
  if q!='tensor-computations/TR-26/README.md':ck('original-input-current-preserved:'+q,read(c,q)==base)
 oldread=old['tensor-computations/TR-26/README.md'];newread=new['tensor-computations/TR-26/README.md'];text=newread.decode();oldtext=oldread.decode()
 ck('complete-earlier-README-verbatim-in-three-archives',all(b==oldread for b in [new['tensor-computations/TR-26/ORIGINAL.md'],package['sources/ORIGINAL.md'],read(c,'docs/lean/statements/TR-26/ORIGINAL.md')]))
 ck('entire-mathematical-and-historical-suffix-unchanged',text[text.index('## Problem statement'):]==oldtext[oldtext.index('## Problem statement'):])
 start=text.index('## Lean proof and verification evidence');end=text.index('## Problem statement')
 stripped=text[:start]+text[end:];stripped=stripped.replace('**Status:** Lean verified','**Status:** Solved').replace('**Last checked:** 2026-10-26','**Last checked:** 2026-09-11')
 ck('only-approved-status-date-and-Lean-evidence-preamble-added',stripped==oldtext)
 formal=json.loads(package['formalization.yaml']);prior=json.loads(oldpackage['formalization.yaml'])
 ck('promotion-status-whole-exact-full-target',formal['status']['phase']=='full-target-verified' and formal['status']['canonical_status']=='Lean verified' and formal['status']['whole_problem_verified'] is True and formal['status']['sorry_count']==0)
 ck('three-status-results-and-standard-axioms-preserved',[x['declaration'] for x in formal['status']['main_results']]==NAMES and formal['status']['axioms']==prior['status']['axioms'])
 ck('no-premature-final-promotion-receipt-claim',all('has its own source-bound final receipt' not in x['verification_status'] for x in formal['status']['main_results']))
 for k in set(prior)-{'status','fidelity','review','project'}:ck('unchanged-metadata-field:'+k,formal[k]==prior[k])
 for k in set(prior['project'])-{'description'}:ck('unchanged-project-metadata-field:'+k,formal['project'][k]==prior['project'][k])
 for x,y in zip(formal['status']['main_results'],prior['status']['main_results']):ck('unchanged-mathematical-result-metadata:'+x['declaration'],{k:v for k,v in x.items() if k!='verification_status'}=={k:v for k,v in y.items() if k!='verification_status'})
 counts=Counter()
 for ident,path in registry.items():
  s=re.search(rb'\*\*Status:\*\* ([^\r\n]+)',new[path]);ck('registered-page-retains-status:'+ident,s is not None)
  counts[s[1].decode().strip()]+=1
 ck('independent-canonical-catalog-count86verified32Solved',counts['Lean verified']==86 and counts['Solved']==32 and sum(counts.values())==217)
 for q in ['README.md','CATALOG.md']:ck('generated-summary-counts:'+q,b'32 solved (published or independently audited); 86 solved with Lean verification.' in new[q])
 inv=json.loads(new['docs/lean/statements/inventory.json']);priorinv=json.loads(old['docs/lean/statements/inventory.json']);entry=next(x for x in inv['entries'] if x['id']=='TR-26');prev=next(x for x in priorinv['entries'] if x['id']=='TR-26')
 ck('TR26-inventory-status-and-canonical-byte-hash',entry['status']=='Lean verified' and entry['canonical_sha256']==sha(newread) and entry['published_sha256']==prev['published_sha256'] and entry['canonical_path']==prev['canonical_path'] and entry['canonical_unchanged_from_base'] is False)
 ck('all-other216-inventory-entries-unchanged',[x for x in inv['entries'] if x['id']!='TR-26']==[x for x in priorinv['entries'] if x['id']!='TR-26'])
 linux=json.loads(new[CAMP+'/FULL_LINUX_CANDIDATE_EXPORTS.json']);ck('candidate-receipt-bound-to-exact-approved-fa85',linux['source_head']==BASE and not linux.get('inventory_independent_export_pending',True))
 for q,e in linux['files'].items():
  b=new[CAMP+'/linux-full-candidate-fa85/'+q];ck('verbatim-Linux-evidence-export:'+q,sha(b)==e['sha256'] and len(b)==e['bytes'])
 receipt=json.loads(new[CAMP+'/linux-full-candidate-fa85/inventory-independent/INVENTORY_REVIEW.json'])
 ck('own-exact2934-check-receipt-export-verbatim',receipt['passed'] and receipt['check_count']==2934 and receipt['head']==BASE and sha(new[CAMP+'/linux-full-candidate-fa85/inventory-independent/INVENTORY_REVIEW.json'])=='9de7404a9b21c2e02ddd668cecfc7def09ded7da9c21e36f4b5a736147675344')
 packages=json.loads(new[CAMP+'/FULL_PACKAGE_REVIEW_EXPORTS.json']);ck('two-independent-corrected-package-review-exports',packages['approved_package_ref']==BASE and {e['reviewer'] for e in packages['exports']}=={'inventory','verification'})
 for e in packages['exports']:
  for x in e['copied_verbatim']:
   q=CAMP+'/full-package-review/'+e['reviewer']+'/'+x['path'];b=new[q];ck('verbatim-package-review-export:'+q,sha(b)==x['sha256'] and len(b)==x['bytes'])
 receiptmd=new[DOC+'/LINUX_CI_RECEIPT.md'].decode();ck('candidate-receipt-and-promotion-receipt-clearly-separated','That final run is pending at this checkpoint.' in receiptmd and 'unused helpers' in receiptmd)
 ck('all-genuine-Linux-identities-described-correctly',all(t in receiptmd for t in [BASE,'40396604016','121831441827','12688115670','68b328659b93033184fd5d65316ef7abcaca9aab','f5f55dd18b6e3f92a6d504d4e5390f975bfe42ead6c3adbd2e72008dda2c279f','b5d6d9a95d39cbd4177769742ed1f00e06ec2f58c4b0bee5eef8e61121b366b3']))
 return dict(commit=c,accepted_candidate=BASE,proof_source_ref=SOURCE,package_input_count=len(package),all_package_sha256={q:sha(b) for q,b in sorted(package.items())},canonical_changed=changed,runtime84_unchanged=True,executable_and_pin92_unchanged=True,canonical_counts=dict(counts),Linux_final_promotion_receipt_pending=True)
error=None
try:details=audit()
except Exception as e:error=str(e)
report=dict(reviewer='/root/inventory',scope='Independent immutable metadata/status promotion and preservation review; no new Lean or Linux run.',passed=error is None,error=error,check_count=len(checks),checks=checks,driver_sha256=sha(Path(__file__).read_bytes()),**details)
(out/'PROMOTION_REVIEW.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k] for k in ['passed','error','check_count']}));raise SystemExit(0 if report['passed'] else 1)
