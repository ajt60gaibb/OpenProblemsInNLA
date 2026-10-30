#!/usr/bin/env python3
"""Read-only inspection of exact unapplied TR04 descriptive proposal revision2."""
import pathlib,json,hashlib
import yaml,jsonschema
HERE=pathlib.Path(__file__).resolve().parent;REPO=HERE.parents[5];DOC=HERE.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
proposal=DOC/'promotion-draft/PROMOTION_PROPOSAL.json';assert sha(proposal)=='c352fedca0c34cf23c89e41fdc82cb870ff552b5d50c6fe01a1fc6b5d47a11b0';p=json.loads(proposal.read_text());assert p['revision']==2 and p['phase']=='proposed descriptive promotion, not yet applied'
freeze=DOC/'CANONICAL_PACKAGE_PREACCEPTANCE_FREEZE_2026-10-26.json';original=json.loads(freeze.read_text())['inputs'];assert len(original)==205
for q,h in original.items():assert sha(REPO/'tensor-computations/TR-04/lean'/q)==h
assert len(p['proposed_replacements'])==2
for r in p['proposed_replacements']:assert sha(REPO/r['destination'])==r['current_sha256'] and sha(REPO/r['proposed_path'])==r['proposed_sha256']
assert {r['destination'] for r in p['proposed_replacements']}=={'tensor-computations/TR-04/lean/formalization.yaml','tensor-computations/TR-04/README.md'}
post=p['post_promotion_package_inputs'];assert set(post)==set(original) and [q for q in original if post[q]!=original[q]]==['formalization.yaml']
assert post['formalization.yaml']=='1302638065dbc0a3ea98b0b0730811b1b8828ddb95ac06441e400bcb11249633'
assert sum(q.endswith('.lean') for q in post)==190 and all(post[q]==h for q,h in original.items() if q.endswith('.lean'))
lock=json.loads((REPO/'tensor-computations/TR-04/lean/proof-source-lock.json').read_text());assert len(lock['copies'])==184
for c in lock['copies']:assert sha(REPO/c['source'])==sha(REPO/c['destination'])==c['source_sha256']==c['destination_sha256']
archive=json.loads((REPO/p['preserved_original_archive']).read_text());assert len(archive['records'])==25
for r in archive['records']:assert sha(REPO/r['original_path'])==sha(REPO/r['archive_path'])==r['sha256']
assert len(json.loads((REPO/'problem_ids.json').read_text()))==217
for q in ['Challenge.lean','Solution.lean','SPEC.md','README.md']:assert post[q]==original[q]
readme=(DOC/'promotion-draft/input-candidate/problem-README.md').read_bytes();old=(REPO/'tensor-computations/TR-04/README.md').read_bytes();marker=b'## Problem statement\n';assert readme.split(marker,1)[1]==old.split(marker,1)[1]
newprefix=readme.split(b'## Lean verification',1)[0].replace(b'**Status:** Lean verified',b'**Status:** Solved').replace(b'**Last checked:** 2026-10-26',b'**Last checked:** 2026-09-11');assert newprefix==old.split(b'## Lean formalization scaffold',1)[0]
prior=REPO/p['prior_proposal_preserved']['path'];assert sha(prior)==p['prior_proposal_preserved']['sha256']=='ee03f187e19741894e487547220365af7fc8274d987fb0dc105d5cc2c722bdcf'
priorp=json.loads(prior.read_text())
for r in priorp['proposed_replacements']:
 q=prior.parent/'input-candidate'/pathlib.Path(r['proposed_path']).name;assert sha(q)==r['proposed_sha256']
class UniqueSafeLoader(yaml.SafeLoader):
 def construct_mapping(self,node,deep=False):
  self.flatten_mapping(node);out={}
  for key,value in node.value:
   k=self.construct_object(key,deep=deep)
   if k in out:raise ValueError('Duplicate YAML key: '+str(k))
   out[k]=self.construct_object(value,deep=deep)
  return out
meta=yaml.load((DOC/'promotion-draft/input-candidate/formalization.yaml').read_text(),Loader=UniqueSafeLoader);jsonschema.validate(meta,json.loads((REPO/'docs/lean/schema/v0.4.schema.json').read_text()))
assert meta['status']['whole_problem_verified'] is True and meta['status']['canonical_status']=='Lean verified'
assert meta['status']['sorry_count']==meta['status']['sorry_in_definitions']==0
assert 'final promotion receipt pending' in meta['status']['comparator_result'] and p['requires_final_source_bound_Linux_receipt'] is True
names=['candidate_count_le_first_mode','cyclic_window_count_le_first_mode','NLA.TR04.target'];assert [r['declaration'] for r in meta['status']['main_results']]==names
assert [r['axioms'] for r in meta['status']['main_results']]==[[],[],['propext','Classical.choice','Quot.sound']]
linux=DOC/'independent-linux-candidate-algebra/APPROVAL.json';assert sha(linux)==p['candidate_Linux']['independent_795check_approval_sha256'];L=json.loads(linux.read_text());assert L['outcome']=='approved' and L['actual_auditor_checks']==795 and L['actual_Linux_import_build_markers']==187 and L['actual_Linux_proof_build_markers']==179
full=DOC/'independent-full-target-review/ACCEPTANCE.json';assert sha(full)==p['independent_full_source_acceptance_sha256'];F=json.loads(full.read_text());assert F['passed'] and F['proof_source_authorship']==[] and F['fresh_Lean_producers']==190 and F['total_kernel_commands']==198 and F['successful_source_build_and_positive_consumer_commands']==197 and F['expected_Challenge_rejections']==1 and F['retained_original_aggregate_passed'] is False and F['raw_result_relabelled_or_rewritten'] is False
index=DOC/'independent-evidence-index/result-through-full-target-v2.json';I=json.loads(index.read_text());assert I['passed'] and I['approved_scopes']==42 and I['shared_project_Lean_source_union']==187 and I['separate_raw_terminal_validation_passed']
geom=DOC/'independent-canonical-package-geometry/final/result.json';G=json.loads(geom.read_text());assert G['passed'] and G['ordinary_local_sources_fresh']==190 and G['total_kernel_invocations']==195
author=DOC/'tt-full-target-author/result.json';A=json.loads(author.read_text());assert A['passed'] and A['project_modules_rebuilt']==182 and A['successful_commands']==183
for q,h in original.items():assert sha(REPO/'tensor-computations/TR-04/lean'/q)==h
result={'reviewer':'/root/recover_algebra','passed':True,'kind':'source-only exact descriptive promotion proposal review; not applied','proposal_sha256':sha(proposal),'revision':2,'proposed_replacements':p['proposed_replacements'],'all205live_candidate_package_inputs_unchanged':True,'projected_package_change':['formalization.yaml'],'all190Lean184copies_unchanged':True,'problem_statement_complete_suffix_byte_exact':True,'historical_canonical_four_exact':True,'all25original_live_archive_pairs_exact':True,'all217IDs_unchanged':True,'schema_valid':True,'final_source_bound_Linux_receipt_explicitly_pending':True,'evidence_sha256':{str(x.relative_to(REPO)):sha(x) for x in [linux,full,index,geom,author]},'initial_wording_proposal_preserved_sha256':sha(prior),'new_Lean_or_CI_execution':False,'inspector_sha256':sha(pathlib.Path(__file__))}
(HERE/'inspection-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['evidence_sha256','proposed_replacements']},indent=2))
