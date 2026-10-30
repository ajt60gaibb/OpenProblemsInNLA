#!/usr/bin/env python3
"""Read-only locked descriptive-promotion review, no mathematical rebuild."""
import argparse,datetime,hashlib,io,json,subprocess,tarfile
from pathlib import Path
REF='0c6d346763a932eb2d379f555e66d8ab3dbf3255'
PROOF='181c365dc426875aaa61984c901478b1b7c696e6'
PREFIX='randomized-and-low-rank-approximation/RE-06/lean/'
PAGE='randomized-and-low-rank-approximation/RE-06/README.md'
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser()
 for n in ['repo','proposal','output','linux_review']:p.add_argument('--'+n.replace('_','-'),type=Path,required=True)
 a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);checks=[];bindings=[]
 def ck(n,v,**d):
  checks.append({'check':n,'pass':bool(v),**d})
  if not v:raise RuntimeError('Failed check: '+n)
 def blob(p,r=REF):return subprocess.check_output(['git','-C',str(a.repo),'show',r+':'+p])
 packetraw=(a.proposal/'PROMOTION_PACKET.json').read_bytes();packet=json.loads(packetraw);proposed={p.name:p.read_bytes() for p in a.proposal.iterdir() if p.is_file()}
 ck('exact_locked_packet_set',set(proposed)==set(packet['files'])|{'PROMOTION_PACKET.json'})
 for n,e in packet['files'].items():ck('proposal_input:'+n,sha(proposed[n])==e['sha256'] and len(proposed[n])==e['bytes'])
 frozen=a.output/'frozen-proposal';frozen.mkdir(exist_ok=True)
 for n,b in proposed.items():(frozen/n).write_bytes(b)
 ck('exact_candidate_and_proof_refs',packet['candidate_ref']==REF and packet['proof_source_ref']==PROOF and packet['candidate_lock_sha256']=='7bfbc8d0493068bce0abcf6d239b539e047061bc5139ce1720e02c64b5592153')
 archive=subprocess.check_output(['git','-C',str(a.repo),'archive',REF,PREFIX]);base={}
 with tarfile.open(fileobj=io.BytesIO(archive)) as tf:
  for e in tf:
   if e.isfile():base[e.name[len(PREFIX):]]=tf.extractfile(e).read()
 ck('295_immutable_base_package_inputs',len(base)==295 and sha(base['PACKAGE_LOCK.json'])==packet['candidate_lock_sha256'])
 virtual=dict(base);virtual['formalization.yaml']=proposed['formalization.yaml'];virtual['PACKAGE_LOCK.json']=proposed['PACKAGE_LOCK.json']
 if 'lean-README.md' in proposed:virtual['README.md']=proposed['lean-README.md']
 if 'lean-README.md' in proposed:
  ck('exact_corrected_v2_packet',sha(packetraw)=='5712b7add2bb2fca11062bd6f83b482a74b6c087579b270505e0492cac5db845' and packet['proposed_lock_sha256']=='e712ded5fbc472ab9fa999de9a1fa885aa86b0b88276f2a55afbc01a7a7a921a')
  ck('complete_candidate_README_archived',proposed['CANDIDATE_README.md']==base['README.md'])
  ck('new_package_README_truthful_current_and_future_scopes',b'This is an unpromoted candidate' not in proposed['lean-README.md'] and b'no final promoted-run receipt is claimed here yet' in proposed['lean-README.md'] and b'87-module Challenge/Solution import closure, including 81 production proof modules' in proposed['lean-README.md'])
  ck('lock_scope_current_and_future_final_gate',b'unpromoted' not in json.loads(proposed['PACKAGE_LOCK.json'])['scope'].encode() and 'final source-bound Linux receipt required before evidence sealing' in json.loads(proposed['PACKAGE_LOCK.json'])['scope'])
  prior=Path(__file__).resolve().parent/'v1/frozen-proposal'
  ck('explicit_v1_same_descriptive_bytes',all(proposed[n]==(prior/n).read_bytes() for n in ['ORIGINAL.md','canonical-README.md','formalization.yaml','proof-README.md']) and packet['supersedes']['packet_sha256']==sha((prior/'PROMOTION_PACKET.json').read_bytes()))
 changed=sorted(n for n in base if base[n]!=virtual[n]);ck('only_explicit_descriptive_canonical_delta',set(changed)==set(packet['allowed_changed_canonical_inputs']) and set(changed)<={'formalization.yaml','PACKAGE_LOCK.json','README.md'},changed=changed)
 lock=json.loads(virtual['PACKAGE_LOCK.json']);oldlock=json.loads(base['PACKAGE_LOCK.json']);ck('same_294_locked_set_plus_self',len(lock['files'])==294 and set(lock['files'])==set(oldlock['files']) and set(virtual)==set(lock['files'])|{'PACKAGE_LOCK.json'} and lock['proof_source_ref']==PROOF and sha(virtual['PACKAGE_LOCK.json'])==packet['proposed_lock_sha256'])
 for n,e in lock['files'].items():ck('proposed_lock:'+n,sha(virtual[n])==e['sha256'] and len(virtual[n])==e['bytes'])
 runtime={n for n in base if n.endswith('.lean') and not n.startswith('reviews/')};ck('91_runtime_input_set',len(runtime)==packet['runtime_inputs_unchanged']==91)
 for n in sorted(runtime):ck('unchanged_runtime:'+n,virtual[n]==base[n])
 mapping=json.loads(virtual['SOURCE_MAP.json']);ck('same_278_source_copy_map',mapping==json.loads(base['SOURCE_MAP.json']) and len(mapping['copies'])==278)
 for e in mapping['copies']:ck('unchanged_source_archive_copy:'+e['path'],virtual[e['path']]==base[e['path']] and sha(virtual[e['path']])==e['sha256'] and len(virtual[e['path']])==e['bytes'])
 ids=blob('problem_ids.json');ck('all217_registry_bytes_and_paths_unchanged',len(json.loads(ids))==217 and ids==blob('problem_ids.json','099805ef1ce7347d373e47cccc3b2d7cf580a99e') and json.loads(ids)['RE-06']==PAGE)
 original=blob(PAGE);ck('complete_previous_canonical_page_archived',proposed['ORIGINAL.md']==original)
 marker=b'## Context and notation\n';oldi=original.index(marker);new=proposed['canonical-README.md'];newi=new.index(marker);ck('complete_Context_through_EOF_suffix_identical',new[newi:]==original[oldi:])
 oldprefix=original[:oldi];expectedprefix=oldprefix.replace(b'**Status:** Solved\n',b'**Status:** Lean verified\n').replace(b'**Last checked:** 2026-09-13\n',b'**Last checked:** 2026-10-26\n');ck('only_status_date_and_new_evidence_section_in_prefix',new.startswith(expectedprefix) and new[len(expectedprefix):newi].lstrip().startswith(b'## Lean proof and verification evidence') and new.count(b'## Lean proof and verification evidence')==1)
 meta=json.loads(virtual['formalization.yaml']);oldmeta=json.loads(base['formalization.yaml']);names=json.loads(virtual['comparator.json'])['theorem_names'];ck('same_six_results_and_all_theorem_semantics',len(names)==6 and [e['declaration'] for e in meta['status']['main_results']]==names and all({k:v for k,v in x.items() if k!='verification_status'}=={k:v for k,v in y.items() if k!='verification_status'} for x,y in zip(oldmeta['status']['main_results'],meta['status']['main_results'])) and meta['fidelity']==oldmeta['fidelity'] and meta['toolchain']==oldmeta['toolchain'] and meta['automation']==oldmeta['automation'] and meta['sources']==oldmeta['sources'])
 ck('promotion_status_fields',meta['status']['phase']=='full-target-verified' and meta['status']['whole_problem_verified'] is True and meta['status']['canonical_status']=='Lean verified')
 ck('every_result_explicitly_future_final_receipt',all('will receive a separate source-bound final Linux receipt before evidence sealing' in e['verification_status'] for e in meta['status']['main_results']))
 ck('proof_record_future_final_receipt_and_exact_linux_counts',b'will receive a separate actual Linux receipt before final evidence sealing' in proposed['proof-README.md'] and b'87-module Challenge/Solution import closure, including 81 production proof modules' in proposed['proof-README.md'] and b'four additional live audit/mirror wrappers were separately compiled locally' in proposed['proof-README.md'])
 # Bind the two genuinely independent source approvals and two package approvals.
 sourceown=a.repo/'reviews/2026-10-23-solved-lean/re06-full-source-review/verification/APPROVAL.json';o=json.loads(sourceown.read_text());ck('own_full_source_approval',o['approved'] and o['non_author'] and o['source_commit']==PROOF)
 otherraw=blob('docs/lean/proofs/RE-06/campaign-2026-10-26/full-source-review/crosscheck/APPROVAL.json','baad44b0dc1e0facf9a8824f78c4f69efa47129f');other=json.loads(otherraw);ck('other_full_source_approval',other['decision']=='approve' and other['independent_non_author'] and other['exact_commit']==PROOF and other['blocking_findings']==[] and other['reviewer']!=o['reviewer'])
 pkgown=a.repo/'reviews/2026-10-23-solved-lean/re06-package-review/verification/APPROVAL.json';po=json.loads(pkgown.read_text());ck('own_exact_candidate_package_approval',po['approved'] and po['non_author'] and po['package_commit']==REF and po['package_lock_sha256']==packet['candidate_lock_sha256'])
 pkgother=a.repo/'reviews/2026-10-23-solved-lean/re06-package-review/inventory/REVIEW.json';pi=json.loads(pkgother.read_text());ck('other_exact_candidate_package_approval',pi['passed'] and pi['reviewed_commit']==REF and pi['package_lock_sha256']==packet['candidate_lock_sha256'] and pi['findings_current_v2']==[] and pi['reviewer']!=po['reviewer'])
 for label,b in [('own-source-APPROVAL.json',sourceown.read_bytes()),('other-source-APPROVAL.json',otherraw),('own-package-APPROVAL.json',pkgown.read_bytes()),('inventory-package-REVIEW.json',pkgother.read_bytes())]:
  f=a.output/'gate-receipts'/label;f.parent.mkdir(exist_ok=True);f.write_bytes(b);bindings.append({'role':label,'sha256':sha(b)})
 # This is a check of the sealed independent audit, not a new Linux execution.
 lr=a.linux_review;la_raw=(lr/'APPROVAL.json').read_bytes();la=json.loads(la_raw);ck('independent_actual_linux_approval',la['decision']=='approve_actual_Linux_Comparator_receipt' and la['non_author'] and la['source_head']==REF and la['run']==40415515989 and la['job']==121897153349 and la['export_count']==6 and la['actual_Comparator_accepted'] and la['actual_LeanCert_kernel_checked'] and la['actual_six_genuine_theorems'] and la['actual_controls_and_isolation'] and la['blocking_findings']==[])
 mf=json.loads((lr/'FILE_SHA256.json').read_text())
 for n,e in mf['files'].items():
  b=(lr/n).read_bytes();ck('sealed_linux_review_byte:'+n,sha(b)==e['sha256'] and len(b)==e['bytes'])
 result_raw=(lr/la['accepted_result']).read_bytes();rr=json.loads(result_raw);ck('accepted1546_actual_offline_checks',sha(result_raw)==la['accepted_result_sha256'] and rr['passed'] and len(rr['checks'])==1546 and all(c['passed'] for c in rr['checks']))
 ck('head_vs_executed_merge_explicit',la['actually_executed_merge']=='1322d6c23e833cba4223b466a3717af1a197b904' and la['source_head']==REF and la['actual_Linux_import_modules']==87 and la['actual_Linux_proof_modules']==81 and la['all91_compiled_claim'] is False)
 for n in ['APPROVAL.json','REVIEW.txt','FILE_SHA256.json']:
  b=(lr/n).read_bytes();f=a.output/'gate-receipts'/('linux-'+n);f.write_bytes(b);bindings.append({'role':'linux-'+n,'sha256':sha(b)})
 ck('original_github_zip_and_raw_job_hashes',la['artifact_ZIP_sha256']=='44cc441ef976ff1da8ee765920cc62c1dbffd96eaa0bc6cc410f784c70179eff' and la['raw_job_sha256']=='5fd6c119cb9342e3f10c506281e26b27649b7d796b736b59588ba98f9f47ebd8')
 findings=[]
 stale=b'This is an unpromoted candidate. RE-06 remains Solved' in virtual['README.md']
 historical_scope=(b'package README' in proposed['proof-README.md'] and b'historical' in proposed['proof-README.md'])
 if stale and not historical_scope:findings.append({'id':'P1','scope':'descriptive coherence','finding':'Canonical package README retains present-tense unpromoted/Solved claims while new metadata promotes to verified; no explicit historical scoping in new proof record.','requested_change':'New immutable packet with an updated package README and lock entry, or explicit historical-candidate scoping of the preserved package README. No runtime or source-copy change needed.'})
 # Exact packet bytes must remain unchanged throughout this read-only review.
 ck('proposal_unmodified_during_review',all((a.proposal/n).read_bytes()==b for n,b in proposed.items()))
 r={'reviewer':'/root/verification','non_author':True,'UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'proposal_packet_sha256':sha(packetraw),'proposal_directory':str(a.proposal),'candidate_ref':REF,'proof_source_ref':PROOF,'mechanical_checks_pass':all(c['pass'] for c in checks),'approved':not findings,'scope':'Descriptive promotion proposal only; no Lean rerun, new Linux execution or final promoted receipt claimed','checks':checks,'findings':findings,'gate_receipt_bindings':bindings,'canonical_changed_inputs':changed,'runtime_inputs_unchanged':91,'mapped_copies_unchanged':278,'script_sha256':sha(Path(__file__).read_bytes())}
 (a.output/'result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'mechanical_checks_pass':r['mechanical_checks_pass'],'checks':len(checks),'approved':r['approved'],'findings':findings}),flush=True)
if __name__=='__main__':main()
