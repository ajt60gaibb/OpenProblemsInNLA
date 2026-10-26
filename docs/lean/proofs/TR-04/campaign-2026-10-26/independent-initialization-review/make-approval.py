#!/usr/bin/env python3
"""Seal only a terminal passing independent fresh initializer replay."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json

BASE=Path(__file__).resolve().parent
REPO=BASE.parents[5]
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'path':str(p.relative_to(REPO)),'sha256':sha(p)}

root=BASE/'run-attempt-1'
r=json.loads((root/'result.json').read_text())
c=json.loads((BASE/'source-lock.json').read_text())
b=c['blocks'][0];br=r['blocks']['initialization']
assert r['passed'] and r['project_sources']==71 and len(r['commands'])==72
assert r['source_lock_sha256']==sha(BASE/'source-lock.json')
assert r['driver_sha256']==sha(BASE/'replay.py') and r['inventory_sha256']==sha(BASE/'source_inventory.py')
assert len(r['declarations'])==870 and len(r['private_or_local_named_declarations'])==55
assert len(b['owned_declarations'])==82 and len(b['author_selected_public_declarations'])==55
assert br['passed'] and br['all_named_declaration_checks_passed'] and br['actual_name_bindings_passed']
assert br['explicit_named_declarations']==870 and br['literal_examples']==39
assert br['actual_owned_kernel_theorem_count']==67
assert br['observed_axioms']==['Classical.choice','Quot.sound','propext']
assert r['lean_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
assert r['project_objects_reused'] is False and r['pinned_external_dependency_objects_reused']
assert all(v['passed'] for k in ['dependencies_before','dependencies_after','original25_before','original25_after'] for v in r[k])
assert all(r['source_unchanged_after'].values()) and all(r['author_locks_unchanged_after'].values())
for name,digest in r['source_sha256'].items():
    assert sha(root/'sources'/name)==sha(REPO/'lean-statements'/name)==digest
for name,digest in r['consumer_sha256'].items(): assert sha(root/'sources'/name)==digest
for cmd in r['commands']: assert cmd['exit_code']==0 and sha(root/cmd['log'])==cmd['log_sha256']
transition=json.loads((BASE/'author-transition-and-controls.json').read_text())
assert transition['passed'] and not transition['old_author_attempt_accepted']
for name,digest in transition['artifact_hashes'].items(): assert sha(REPO/name)==digest
fixture=json.loads((BASE/'private-auditor-preflight-2/result.json').read_text())
assert fixture['passed'] and fixture['driver_sha256']==r['driver_sha256']
assert fixture['custom_axiom_hidden_in_private_theorem_rejected'] and not fixture['negative_control_accepted_as_a_proof']
approval={
 'passed':True,'approval':'APPROVED_FROZEN_ACTUAL_ORIGINAL_START_TO_FIRST_SVD_INITIALIZER_ONLY',
 'reviewer':'/root/recover_verification','proof_source_authorship':[],
 'recorded_utc':datetime.now(timezone.utc).isoformat(),
 'execution_started_utc':r['started_utc'],'execution_finished_utc':r['finished_utc'],
 'author':b['author'],'author_source_lock':{'path':b['author_lock_path'],'sha256':b['author_lock_sha256']},
 'independent_source_lock':ref(BASE/'source-lock.json'),'result':ref(root/'result.json'),
 'scoped_kernel_result':br,
 'source_review':[
  'All six frozen source bodies were independently read. The scalar block proves literal instructions144..166, including the actual read of memory at the order header before rank decoding and ordinary branch min computations; no instruction or result is supplied as an evaluator premise.',
  'The generic installed-header proofs preserve all natural registers outside their actual small frame. The suffix call needs only the stated actual memory cell equations and start/register fields; it does not assume decoded values are already in registers. The first requested rank is read from literal original InputMemory at address order.',
  'The composed initializer starts with the literal original Start. It proves actual header-product return, dispatch tag0,25-step allocation startup, actual first-mode decoding, suffix-product call, actual first-rank decoding, dispatch and capped-dimension branches. It reaches running label167 with all17 allocation fields, candidate index zero, unchanged original memory, rows/columns/requested rank/minimum/cap equal to their original-data definitions.',
  'The ttInitial_svd_ready endpoint quantifies every original Shape, Ranks, tensor and legal trace, including zero requested ranks. Its prefix time and actual CostThrough are bounded by102*(Size+1). It ends before execution of the SVD instruction and does not assert completion of the whole TT program.',
  'Every one of870 explicitly named declarations across the fresh71-source closure receives actual ConstantInfo-kind, genuine LeanCert kernel and transitive axiom checks. This includes all82 new explicit names,27 new private helpers and the Prop-valued named NeZero instance. The exact module-qualified compiler private names are checked without suffix search. Anonymous/generated helpers are covered by kernel compilation and transitive axioms, not claimed as separate explicit-name assertions.',
  'All39 complete public theorem binder/type headers were copied verbatim from the frozen sources, including compact term-proof declarations and let-valued conclusions; only their proof terms are applications of the actual original theorem. Two additional consumers derive actual first-SVD output-block separation from the computed original dimensions/allocation, and prove the zero-requested-rank trace endpoint including unchanged memory and charged prefix bound.',
  'The author first run remains false: all71 sources compiled but the generated consumer failed. Final author lock de601 differs from original cb4 solely in execution timestamp; all71 records,55 selected declarations, targets and originals are identical. The corrected author attempt and independent fresh run are separate receipts. The private/local auditor positive fixture passes, and its hidden custom-axiom negative fixture is rejected by the actual LeanCert kernel assertion.'
 ],
 'verification_counts':{'fresh_project_sources':71,'fresh_consumer_commands':1,'successful_commands':72,
    'distinct_explicit_named_checks':870,'explicit_private_named_checks':55,'new_explicit_names':82,
    'new_private_names':27,'new_actual_theorem_kinds':67,'verbatim_public_type_examples':39,'additional_actual_trace_examples':2,
    'clean_dependency_pins':10,'original_inputs_preserved':25},
 'limits':'Actual original initialization through first SVD entry only. Every future SVD reply, candidate loop, recursive child execution, reverse/lift/error selection, global approximation and total full-program cost/Target/authoritative CI remain separate obligations.',
 'retained_failed_author_attempt':{'source_lock':ref(BASE.parent/'tt-initialization-author/source-lock.json'),
    'failure_record':ref(BASE.parent/'tt-initialization-author/ATTEMPT_FAILED.json'),'accepted_as_proof':False},
 'author_transition_and_auditor_controls':ref(BASE/'author-transition-and-controls.json'),
 'independent_private_name_provenance':ref(BASE/'private-name-provenance.json'),
 'reproducers':[ref(BASE/name) for name in ['prepare.py','make-replay.py','replay.py','source_inventory.py','integration-initialization.lean.txt','check-private-auditor-current.py','check-author-transition.py','make-approval.py']],
 'project_objects_reused':False,'pinned_external_objects_reused':True,'observed_axioms':br['observed_axioms'],
 'proof_source_changes':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
(BASE/'APPROVAL.json').write_text(json.dumps(approval,indent=2)+'\n')
print(json.dumps({'passed':True,'approval_sha256':sha(BASE/'APPROVAL.json'),'result_sha256':sha(root/'result.json')},indent=2))
