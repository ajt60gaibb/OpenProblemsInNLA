#!/usr/bin/env python3
"""Read-only artifact integrity check; does not run Lean or establish new proof acceptance."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5];PROOFS=REPO/'docs/lean/proofs/TR-04'
def sha(p):
 assert p.is_file() and not p.is_symlink(),str(p)
 return hashlib.sha256(p.read_bytes()).hexdigest()
artifacts={}
def bind(p):
 digest=sha(p);artifacts[str(p.relative_to(REPO))]=digest;return digest
specs=[
 ('first_five_partial','campaign-2026-10-25/independent-batch-review','run-attempt-1',False),
 ('corrected_memory','campaign-2026-10-25/independent-svd-memory-review','run-attempt-1',True),
 ('strict_math','campaign-2026-10-25/independent-strict-math-review','run-attempt-1',True),
 ('machine_components','campaign-2026-10-26/independent-machine-components','run-attempt-2',True),
 ('explicit_math','campaign-2026-10-26/independent-explicit-frame-review','run-attempt-1',True),
 ('original_machine','campaign-2026-10-26/independent-original-machine-review','run-attempt-1',True),
 ('frame_gather','campaign-2026-10-26/independent-frame-gather-review','run-attempt-2',True),
 ('header_bank','campaign-2026-10-26/independent-header-bank-review','run-attempt-1',True),
 ('threshold_scan','campaign-2026-10-26/independent-threshold-scan-review','run-attempt-1',True),
 ('selector_tensor','campaign-2026-10-26/independent-selector-tensor-review','run-attempt-1',True),
 ('layout_assembly','campaign-2026-10-26/independent-layout-assembly-review','run-attempt-2',True),
 ('dimensions','campaign-2026-10-26/independent-dimension-review','run-attempt-2',True),
 ('main_phases','campaign-2026-10-26/independent-main-phases-review','run-attempt-2',True),
 ('initialization','campaign-2026-10-26/independent-initialization-review','run-attempt-1',True),
 ('forward_gather','campaign-2026-10-26/independent-forward-gather-review','run-attempt-1',True),
 ('initial_family_child','campaign-2026-10-26/independent-initial-family-child-review','run-attempt-1',False),
 ('corrected_child_initialization','campaign-2026-10-26/independent-child-initialization-review','run-attempt-1',True),
 ('reverse_final_child_svd','campaign-2026-10-26/independent-reverse-final-review','run-attempt-2',True)]
results=[];source_union={}
for key,directory,run,passed in specs:
 directory=PROOFS/directory;root=directory/run;p=root/'result.json';d=json.loads(p.read_text());assert d['passed']==passed
 assert bind(directory/'replay.py')==d['driver_sha256'] and bind(directory/'source-lock.json')==d['source_lock_sha256']
 assert bind(directory/'source_inventory.py')==d['inventory_sha256']
 assert d['project_objects_reused'] is False and d['pinned_external_dependency_objects_reused'] is True
 assert all(v['passed'] for k in ['dependencies_before','dependencies_after','original25_before','original25_after'] for v in d[k])
 assert all(d['source_unchanged_after'].values()) and all(d['author_locks_unchanged_after'].values())
 for name,digest in d['source_sha256'].items():
  assert bind(root/'sources'/name)==digest
  assert sha(REPO/'lean-statements'/name)==digest
  if name in source_union:assert source_union[name]==digest
  source_union[name]=digest
 for name,digest in d['consumer_sha256'].items():assert bind(root/'sources'/name)==digest
 for c in d['commands']:assert bind(root/c['log'])==c['log_sha256']
 failures=[{'source':c['source'],'exit_code':c['exit_code']} for c in d['commands'] if c['exit_code']]
 if not passed:
  if key=='initial_family_child':
   assert failures==[{'source':'Independent_child_initialization_Consumer.lean','exit_code':1}]
   assert d['blocks']['initial_family']['passed'] and not d['blocks']['child_initialization']['passed']
  else:
   assert failures==[{'source':'Independent_svd_memory_Consumer.lean','exit_code':1}]
   assert all(d['blocks'][k]['passed'] for k in ['recursive_tensor','svd_tie','scalar_programs','radix_interface'])
   assert not d['blocks']['svd_memory']['passed']
 else:assert not failures and all(v['passed'] for v in d['blocks'].values())
 results.append({'key':key,'path':str(p.relative_to(REPO)),'sha256':bind(p),'expected_aggregate_passed':passed,'commands':len(d['commands']),'retained_failures':failures})
acceptance_paths=[PROOFS/'campaign-2026-10-25/independent-batch-review/FIVE_BLOCK_ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-machine-components/ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-explicit-frame-review/ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-original-machine-review/ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-selector-tensor-review/ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-layout-assembly-review/ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-main-phases-review/ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-forward-gather-review/ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-initial-family-child-review/TWO_SCOPE_ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-reverse-final-review/ACCEPTANCE.json']
approval_paths=[PROOFS/'campaign-2026-10-25/independent-strict-math-review/APPROVAL.json',PROOFS/'campaign-2026-10-26/independent-frame-gather-review/APPROVAL.json',PROOFS/'campaign-2026-10-26/independent-header-bank-review/APPROVAL.json',PROOFS/'campaign-2026-10-26/independent-threshold-scan-review/APPROVAL.json',PROOFS/'campaign-2026-10-26/independent-dimension-review/APPROVAL.json',PROOFS/'campaign-2026-10-26/independent-initialization-review/APPROVAL.json']
for p in acceptance_paths:
 d=json.loads(p.read_text());assert d['passed'];bind(p)
 for v in d.get('reproducers',[]):assert bind(REPO/v['path'])==v['sha256']
 for v in d['receipts']:
  q=REPO/v['path'];assert bind(q)==v['sha256'];approval_paths.append(q)
for p in approval_paths:
 d=json.loads(p.read_text());assert d['passed'] and d['reviewer']=='/root/recover_verification'
 assert not d['proof_source_authorship'] and d['full_TR04_Target_proved'] is False and d['authoritative_Linux_Comparator'] is False
 lock=d['author_source_lock'];assert bind(REPO/lock['path'])==lock['sha256']
 evidence=d.get('result',d.get('retained_partial_batch_result'));assert bind(REPO/evidence['path'])==evidence['sha256']
 bind(p)
# The earlier squared-error consumer kind failure remains failed, with its exact original driver.
root=PROOFS/'campaign-2026-10-26/independent-machine-components';p=root/'run-attempt-1/result.json';d=json.loads(p.read_text());assert d['passed'] is False
assert bind(root/'replay-attempt-1.py')==d['driver_sha256']
assert [(c['source'],c['exit_code']) for c in d['commands'] if c['exit_code']]==[('Independent_squared_error_Consumer.lean',1)]
for c in d['commands']:assert bind(root/'run-attempt-1'/c['log'])==c['log_sha256']
bind(p);bind(root/'kind-classification-diagnostic.json')
# The extra frame-composition consumer failure is retained separately from its corrected fresh replay.
root=PROOFS/'campaign-2026-10-26/independent-frame-gather-review';p=root/'run-attempt-1/result.json';d=json.loads(p.read_text());assert d['passed'] is False
assert bind(root/'replay.py')==d['driver_sha256']
assert [(c['source'],c['exit_code']) for c in d['commands'] if c['exit_code']]==[('Independent_frame_gather_Consumer.lean',1)]
for c in d['commands']:assert bind(root/'run-attempt-1'/c['log'])==c['log_sha256']
for name,digest in {**d['source_sha256'],**d['consumer_sha256']}.items():assert bind(root/'run-attempt-1/sources'/name)==digest
bind(p);bind(root/'integration-diagnostic.json');bind(root/'integration-examples-attempt-1.lean.txt')
for directory in ['independent-frame-gather-review','independent-header-bank-review','independent-threshold-scan-review']:
 bind(PROOFS/'campaign-2026-10-26'/directory/'integration-examples.lean.txt')
for key in ['selector','tensor_operations']:
 bind(PROOFS/'campaign-2026-10-26/independent-selector-tensor-review'/('integration-'+key+'.lean.txt'))
# The concrete assembly-site consumer syntax failure remains false and fully retained.
root=PROOFS/'campaign-2026-10-26/independent-layout-assembly-review';p=root/'run-attempt-1/result.json';d=json.loads(p.read_text());assert d['passed'] is False
assert bind(root/'replay.py')==d['driver_sha256']
assert [(c['source'],c['exit_code']) for c in d['commands'] if c['exit_code']]==[('Independent_assembly_Consumer.lean',1)]
for c in d['commands']:assert bind(root/'run-attempt-1'/c['log'])==c['log_sha256']
for name,digest in {**d['source_sha256'],**d['consumer_sha256']}.items():assert bind(root/'run-attempt-1/sources'/name)==digest
bind(p);bind(root/'consumer-syntax-diagnostic.json');bind(root/'integration-assembly-attempt-1.lean.txt')
for key in ['layout','assembly']:bind(root/('integration-'+key+'.lean.txt'))
p=root/'auxiliary-input-check.json';d=json.loads(p.read_text());assert d['passed'];bind(p)
assert bind(root/'generator-check.log')==d['generator_check']['log_sha256']
for v in d['support_inputs']+d['author_results']+[d['retained_layout_superseded_lock'],d['retained_layout_initial_diagnostic']]:assert bind(REPO/v['path'])==v['sha256']
assert not d['retained_layout_superseded_lock']['accepted_as_final'] and not d['retained_layout_initial_diagnostic']['accepted_as_final']
root=PROOFS/'campaign-2026-10-26/independent-dimension-review'
p=root/'run-attempt-1/result.json';d=json.loads(p.read_text());assert d['passed'] is False
assert bind(root/'replay.py')==d['driver_sha256']
assert [(c['source'],c['exit_code']) for c in d['commands'] if c['exit_code']]==[('Independent_dimensions_Consumer.lean',1)]
for c in d['commands']:assert bind(root/'run-attempt-1'/c['log'])==c['log_sha256']
for name,digest in {**d['source_sha256'],**d['consumer_sha256']}.items():assert bind(root/'run-attempt-1/sources'/name)==digest
bind(p);bind(root/'cardinality-consumer-diagnostic.json');bind(root/'integration-dimensions-attempt-1.lean.txt')
bind(root/'integration-dimensions.lean.txt');bind(root/'check-author-history.py');bind(root/'make-approval.py')
p=root/'author-history.json';d=json.loads(p.read_text());assert d['passed'] and not d['interrupted_run_accepted'];bind(p)
assert not d['interrupted_run_terminal_result_present'] and d['source_snapshot_count_each']==27
for name,digest in d['artifact_hashes'].items():assert bind(REPO/name)==digest
# The first main-phase batch remains false, with only Startup terminal-approved.
root=PROOFS/'campaign-2026-10-26/independent-main-phases-review';p=root/'run-attempt-1/result.json';d=json.loads(p.read_text())
assert d['passed'] is False and d['blocks']['startup']['passed']
assert d['blocks']['first_selection']['consumer'] is None
assert bind(root/'replay-attempt-1.py')==d['driver_sha256']
assert bind(root/'source-lock.json')==d['source_lock_sha256']
assert [(c['source'],c['exit_code']) for c in d['commands'] if c['exit_code']]==[('Independent_dispatch_metadata_Consumer.lean',1)]
for c in d['commands']:assert bind(root/'run-attempt-1'/c['log'])==c['log_sha256']
for name,digest in {**d['source_sha256'],**d['consumer_sha256']}.items():assert bind(root/'run-attempt-1/sources'/name)==digest
bind(p);bind(root/'local-instance-context-diagnostic.json')
for key in ['startup','dispatch_metadata','first_selection']:bind(root/('integration-'+key+'.lean.txt'))
p=root/'author-and-control-receipts.json';d=json.loads(p.read_text());assert d['passed'] and len(d['terminal_author_results'])==3;bind(p)
for name,digest in d['artifact_hashes'].items():assert bind(REPO/name)==digest
assert d['private_auditor_positive_and_negative_passed'] and not d['negative_custom_axiom_fixture_accepted_as_proof']
p=root/'private-auditor-preflight-4/result.json';d=json.loads(p.read_text());assert d['passed'];bind(p)
assert bind(root/'replay.py')==d['driver_sha256']
assert d['custom_axiom_hidden_in_private_theorem_rejected'] and not d['negative_control_accepted_as_a_proof']
for c in d['commands']:
 assert c['exit_code']==c['expected_exit_code']
 assert bind(root/'private-auditor-preflight-4'/c['source'])==c['source_sha256']
 assert bind(REPO/c['log'])==c['log_sha256']
assert d['commands'][-1]['expected_exit_code']==1
p=root/'private-name-provenance.json';d=json.loads(p.read_text());bind(p)
assert len(d['private_declarations'])==62 and len({v['name'] for v in d['local_declarations']})==1
assert sha(Path(d['compiler_private_name_support']['path']))==d['compiler_private_name_support']['sha256']
# Bind the failed author initializer consumer without relabeling it accepted.
root=PROOFS/'campaign-2026-10-26/independent-initialization-review'
p=root/'author-transition-and-controls.json';d=json.loads(p.read_text());assert d['passed'];bind(p)
assert d['old_author_attempt_accepted'] is False and d['all_71_source_records_and_55_selected_names_identical']
assert d['author_source_lock_difference']==['execution_started_utc']
for name,digest in d['artifact_hashes'].items():assert bind(REPO/name)==digest
assert d['independent_private_auditor_positive_negative_passed'] and not d['negative_fixture_accepted_as_proof']
for name in ['prepare.py','make-replay.py','driver-provenance.json','integration-initialization.lean.txt','check-private-auditor.py','check-private-auditor-current.py','check-author-transition.py','make-approval.py','private-name-provenance.json']:bind(root/name)
p=root/'private-auditor-preflight-2/result.json';d=json.loads(p.read_text());assert d['passed'];bind(p)
assert bind(root/'replay.py')==d['driver_sha256']
assert d['custom_axiom_hidden_in_private_theorem_rejected'] and not d['negative_control_accepted_as_a_proof']
for c in d['commands']:
 assert c['exit_code']==c['expected_exit_code']
 assert bind(root/'private-auditor-preflight-2'/c['source'])==c['source_sha256']
 assert bind(REPO/c['log'])==c['log_sha256']
assert d['commands'][-1]['expected_exit_code']==1
# Current gather/forward author history and raw literal headers are read-only bindings.
root=PROOFS/'campaign-2026-10-26/independent-forward-gather-review'
p=root/'author-history.json';d=json.loads(p.read_text());assert d['passed'];bind(p)
assert not d['forward_interrupted_run_accepted'] and not d['forward_failed_development_consumer_accepted']
assert d['private_auditor_positive_negative_passed'] and not d['negative_fixture_accepted_as_proof']
for name,digest in d['artifact_hashes'].items():assert bind(REPO/name)==digest
p=root/'raw-literal-header-check.json';d=json.loads(p.read_text());assert d['passed'] and d['header_count']==81;bind(p)
assert bind(root/'replay.py')==d['driver_sha256']
for name in ['driver-provenance.json','private-name-provenance.json']:bind(root/name)
for name in ['check-evidence-through-initialization-attempt-1.py','initialization-index-diagnostic.json']:bind(BASE/name)
# Bind the stopped initial-family author run separately from the corrected fresh author and independent runs.
root=PROOFS/'campaign-2026-10-26/independent-initial-family-child-review'
p=root/'author-history.json';d=json.loads(p.read_text());assert d['passed'];bind(p)
assert not d['old_author_attempt_accepted'] and d['stopped_author_source_successes']==23
assert d['all118_frozen_source_records_and32_public_names_identical']
assert d['old_new_lock_difference_keys']==['consumer_input','execution_started_utc','replay_driver_sha256']
assert d['private_auditor_positive_negative_passed'] and not d['negative_fixture_accepted_as_proof']
for name,digest in d['artifact_hashes'].items():assert bind(REPO/name)==digest
p=root/'raw-literal-header-check.json';d=json.loads(p.read_text());assert d['passed'] and d['header_count']==51;bind(p)
assert bind(root/'replay.py')==d['driver_sha256']
for name in ['driver-provenance.json','private-name-provenance.json']:bind(root/name)
# Corrected child replay keeps the entire earlier failure and exact same literal propositions.
root=PROOFS/'campaign-2026-10-26/independent-initial-family-child-review'
p=root/'TWO_SCOPE_ACCEPTANCE.json';d=json.loads(p.read_text());assert d['passed'];bind(p)
assert d['retained_aggregate_run_passed'] is False and d['old_child_consumer_failure_accepted'] is False
assert not d['unexecuted_full_aggregate_approval_template_accepted']
assert bind(REPO/d['prior_scoped_description_receipt']['path'])==d['prior_scoped_description_receipt']['sha256']
for name in ['zero-header-consumer-diagnostic.json','integration-child_initialization-attempt-1.lean.txt','integration-child_initialization.lean.txt','integration-initial_family.lean.txt','make-approval.py']:bind(root/name)
root=PROOFS/'campaign-2026-10-26/independent-child-initialization-review'
for name in ['driver-provenance.json','private-name-provenance.json','raw-literal-header-check.json','integration-child_initialization.lean.txt']:bind(root/name)
p=root/'raw-literal-header-check.json';d=json.loads(p.read_text());assert d['passed'] and d['header_count']==27
assert bind(root/'replay.py')==d['driver_sha256']
# The newer module-qualified private-name auditor retains both code349..354 sets.
root=PROOFS/'campaign-2026-10-26/independent-reverse-final-review'
p=root/'author-history.json';d=json.loads(p.read_text());assert d['passed'];bind(p)
assert len(d['terminal_author_results'])==4 and not d['reverse_failed_development_consumer_accepted']
assert d['private_identity_positive_and_three_negative_controls_passed'] and not d['negative_fixture_accepted_as_proof']
for name,digest in d['artifact_hashes'].items():assert bind(REPO/name)==digest
p=root/'raw-literal-header-check.json';d=json.loads(p.read_text());assert d['passed'] and d['header_count']==138;bind(p)
assert bind(root/'replay.py')==d['driver_sha256'] and bind(root/'source-lock.json')==d['source_lock_sha256']
p=root/'private-identity-controls/result.json';d=json.loads(p.read_text());assert d['passed'];bind(p)
assert bind(root/'replay.py')==d['driver_sha256']
assert d['two_modules_with_same_private_source_name_checked_distinctly'] and d['private_local_public_kinds_passed']
assert d['hidden_custom_axiom_in_exact_second_module_rejected'] and d['wrong_module_rejected'] and d['wrong_actual_kind_rejected']
assert not d['negative_control_accepted_as_proof']
assert sum(v['expected_exit_code']==1 for v in d['commands'])==3
for cmd in d['commands']:
 assert cmd['exit_code']==cmd['expected_exit_code']
 assert bind(root/'private-identity-controls'/cmd['source'])==cmd['source_sha256']
 assert bind(REPO/cmd['log'])==cmd['log_sha256']
p=root/'private-name-provenance.json';d=json.loads(p.read_text());bind(p)
assert len(d['private_declarations'])==127 and len({v['name'] for v in d['local_declarations']})==1
assert sha(Path(d['compiler_private_name_support']['path']))==d['compiler_private_name_support']['sha256']
for identity,v in d['private_declarations'].items():assert identity==v['actual_kernel_name']
for name in ['driver-provenance.json','consumer-bindings.json']:
 p=root/name if name!='consumer-bindings.json' else root/'run-attempt-2'/name
 bind(p)
# The first newer aggregate remains false; only its extra reverse projection proof failed.
p=root/'run-attempt-1/result.json';d=json.loads(p.read_text());assert d['passed'] is False;bind(p)
assert bind(root/'replay.py')==d['driver_sha256'] and bind(root/'source-lock.json')==d['source_lock_sha256']
assert [(v['source'],v['exit_code']) for v in d['commands'] if v['exit_code']]==[('Independent_reverse_Consumer.lean',1)]
assert d['blocks']['final_callers']['passed'] and d['blocks']['copy349']['passed']
assert d['blocks']['reverse']['all_named_declaration_checks_passed'] and d['blocks']['child_svd_loop']['consumer'] is None
for cmd in d['commands']:assert bind(root/'run-attempt-1'/cmd['log'])==cmd['log_sha256']
for name,digest in {**d['source_sha256'],**d['consumer_sha256']}.items():assert bind(root/'run-attempt-1/sources'/name)==digest
for name in ['reverse-extra-consumer-diagnostic.json','integration-reverse-attempt-1.lean.txt','ReverseConsumerDevelopmentCorrected.lean',
 'reverse-consumer-development-corrected.log','reverse-consumer-development-corrected.json','raw-literal-header-check-attempt-1.json',
 'check-raw-literal-headers-attempt-1.py','make-approval-attempt-1-unexecuted.py']:
 bind(root/name)
p=root/'reverse-consumer-development-corrected.json';d=json.loads(p.read_text())
assert d['passed'] and d['project_objects_reused_for_development_only'] and not d['independent_acceptance']
assert d['empty_object_fresh_repeat_required']
# Retain the prior integrity index and the portability fix for its exact JSON metadata.
p=BASE/'result-through-initial-family-child.json';d=json.loads(p.read_text());assert d['passed'];bind(p)
assert d['approved_scopes']==31 and d['distinct_current_project_Lean_sources']==147
for name,digest in d['artifact_hashes'].items():assert bind(REPO/name)==digest
p=BASE/'metadata-portability-review.json';d=json.loads(p.read_text());assert d['passed'];bind(p)
assert len(approval_paths)==35 and len(source_union)==161
result={'passed':True,'type':'artifact_hash_integrity_only','executed_utc':datetime.now(timezone.utc).isoformat(),'checker_sha256':sha(Path(__file__)),'fresh_Lean_replayed_by_this_check':False,'independent_result_records':results,'approved_scopes':len(approval_paths),'distinct_current_project_Lean_sources':len(source_union),'current_project_source_hashes':source_union,'artifact_hashes':artifacts,'scope_note':'This verifies retained independent receipts and exact current frozen sources. It does not relabel any retained harness failure, perform a new kernel replay, cover every future source, or assert the complete TR04 Target/CI/Comparator. Geometry relocation review is a separate independent receipt.','proof_inputs_changed':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'passed':True,'approved_scopes':len(approval_paths),'distinct_current_project_Lean_sources':len(source_union),'bound_artifacts':len(artifacts),'output_sha256':sha(args.output)},indent=2))
