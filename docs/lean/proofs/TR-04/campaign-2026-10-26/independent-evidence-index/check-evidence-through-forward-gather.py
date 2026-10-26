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
 ('forward_gather','campaign-2026-10-26/independent-forward-gather-review','run-attempt-1',True)]
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
  assert failures==[{'source':'Independent_svd_memory_Consumer.lean','exit_code':1}]
  assert all(d['blocks'][k]['passed'] for k in ['recursive_tensor','svd_tie','scalar_programs','radix_interface'])
  assert not d['blocks']['svd_memory']['passed']
 else:assert not failures and all(v['passed'] for v in d['blocks'].values())
 results.append({'key':key,'path':str(p.relative_to(REPO)),'sha256':bind(p),'expected_aggregate_passed':passed,'commands':len(d['commands']),'retained_failures':failures})
acceptance_paths=[PROOFS/'campaign-2026-10-25/independent-batch-review/FIVE_BLOCK_ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-machine-components/ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-explicit-frame-review/ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-original-machine-review/ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-selector-tensor-review/ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-layout-assembly-review/ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-main-phases-review/ACCEPTANCE.json',PROOFS/'campaign-2026-10-26/independent-forward-gather-review/ACCEPTANCE.json']
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
result={'passed':True,'type':'artifact_hash_integrity_only','executed_utc':datetime.now(timezone.utc).isoformat(),'checker_sha256':sha(Path(__file__)),'fresh_Lean_replayed_by_this_check':False,'independent_result_records':results,'approved_scopes':len(approval_paths),'distinct_current_project_Lean_sources':len(source_union),'current_project_source_hashes':source_union,'artifact_hashes':artifacts,'scope_note':'This verifies retained independent receipts and exact current frozen sources. It does not relabel any retained harness failure, perform a new kernel replay, cover every future source, or assert the complete TR04 Target/CI/Comparator. Geometry relocation review is a separate independent receipt.','proof_inputs_changed':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'passed':True,'approved_scopes':len(approval_paths),'distinct_current_project_Lean_sources':len(source_union),'bound_artifacts':len(artifacts),'output_sha256':sha(args.output)},indent=2))
