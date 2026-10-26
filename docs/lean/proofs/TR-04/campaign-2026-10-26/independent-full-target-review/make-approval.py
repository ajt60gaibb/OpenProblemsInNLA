#!/usr/bin/env python3
"""Seal mathematical/canonical kernel receipts only after all expected outcomes."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
B=Path(__file__).resolve().parent;REPO=B.parents[5]
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'path':str(p.relative_to(REPO)),'sha256':sha(p)}
root=B/'run-attempt-1';r=json.loads((root/'result.json').read_text());c=json.loads((B/'source-lock.json').read_text())
terminal=json.loads((B/'TERMINAL_VALIDATION.json').read_text())
assert terminal['passed'] and terminal['full_TR04_Target_proved'] and terminal['canonical_package_kernel_passed']
assert r['passed'] is False and terminal['retained_original_aggregate_passed'] is False
assert terminal['all7_positive_scopes_rechecked_from_raw_logs'] and terminal['Challenge_target_exact_forbidden_sorryAx_rejected']
assert terminal['retained_original_result']['sha256']==sha(root/'result.json')
for p,h in terminal['artifact_hashes'].items():assert sha(REPO/p)==h
assert r['authoritative_Linux_Comparator'] is False
assert r['project_sources']==190 and len(r['commands'])==198
assert len(r['declarations'])==1821 and len(r['private_or_local_named_declarations'])==181
assert r['driver_sha256']==sha(B/'replay.py') and r['inventory_sha256']==sha(B/'source_inventory.py')
assert r['source_lock_sha256']==sha(B/'source-lock.json') and r['private_name_provenance_sha256']==sha(B/'private-name-provenance.json')
assert r['lean_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
assert '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in r['lean_version']['stdout']
assert r['project_objects_reused'] is False and r['pinned_external_dependency_objects_reused']
assert all(v['passed'] for k in ['dependencies_before','dependencies_after','original25_before','original25_after'] for v in r[k])
assert all(r['source_unchanged_after'].values()) and all(r['shared_original_sources_unchanged_after'].values())
assert all(r['author_locks_unchanged_after'].values()) and r['package_inputs_unchanged_after']
assert len(r['package_input_sha256'])==205 and r['package_input_sha256']==c['package_inputs']
for n,h in r['package_input_sha256'].items():assert sha(root/'sources'/n)==sha(REPO/c['canonical_project']/n)==h
for n,h in r['consumer_sha256'].items():assert sha(root/'sources'/n)==h
for cmd in r['commands']:
    assert cmd['exit_code']==cmd['expected_exit_code'] and sha(root/cmd['log'])==cmd['log_sha256']
assert [v['source'] for v in r['commands'] if v['exit_code']]==['Independent_Challenge_Negative.lean']
negative=dict(r['challenge_negative_control']);assert negative['passed'] is False and negative['actual_exit_code']==1
assert not negative['comparison_target_accepted_as_proof']
negative['raw_terminal_validation']=ref(B/'TERMINAL_VALIDATION.json')
negative['actual_trust_rejection_revalidated']=True
for name in ['canonical-input-review.json','author-terminal-receipts.json','global-inventory-correction.json']:
    d=json.loads((B/name).read_text());assert d['passed']
    for p,h in d.get('artifact_hashes',{}).items():assert sha(REPO/p)==h
assert sha(B/'author-terminal-receipts.json')==r['author_terminal_receipts_sha256']
headers=json.loads((B/'raw-literal-header-check.json').read_text())
assert headers['passed'] and headers['header_count']==80
assert headers['driver_sha256']==r['driver_sha256'] and headers['source_lock_sha256']==r['source_lock_sha256']
control=json.loads((B/'private-identity-controls/result.json').read_text())
assert control['passed'] and control['driver_sha256']==r['driver_sha256']
assert control['hidden_custom_axiom_in_exact_second_module_rejected'] and control['wrong_module_rejected'] and control['wrong_actual_kind_rejected']
assert not control['negative_control_accepted_as_proof']
global_headers=json.loads((B/'global-header-controls/result.json').read_text())
assert global_headers['passed'] and global_headers['driver_sha256']==r['driver_sha256'] and global_headers['project_objects_reused'] is False
git=json.loads((B/'production-harness-proof-commit-binding.json').read_text())
assert git['passed'] and git['metadata']['repository_commit']=='027aaefbadf602ac460d0cf4cae7beed3181d712'
assert git['input_sha256']==c['package_inputs'] and git['all_tracked_files_ordinary_no_tracked_build_cache']
notes=json.loads((B/'source-review-notes.json').read_text())
assert notes['all25_new_shared_source_bodies_read_in_full'] and notes['new_canonical_wrappers_and_retained_originals_read']
assert not notes['proof_source_authorship'] and not notes['proof_source_changes']
receipts=[]
for b in c['blocks']:
    key=b['key'];br=r['blocks'][key]
    assert br['passed'] and br['all_named_declaration_checks_passed'] and br['actual_name_bindings_passed']
    assert br['observed_axioms']==['Classical.choice','Quot.sound','propext']
    assert br['literal_examples']==len(b['literal_endpoints'])
    complete=key in {'full_target','canonical_solution'}
    approval={'passed':True,'approval':'APPROVED_LITERAL_COMPLETE_ORIGINAL_TARGET_AND_CANONICAL_PROOF_KERNEL_ONLY' if complete else 'APPROVED_FROZEN_'+key.upper()+'_SUPPORT_SCOPE_ONLY',
     'recorded_utc':datetime.now(timezone.utc).isoformat(),'execution_started_utc':r['started_utc'],'execution_finished_utc':r['finished_utc'],
     'reviewer':'/root/recover_verification','proof_source_authorship':[],'author':b['author'],
     'author_source_lock':{'path':b['author_lock_path'],'sha256':b['author_lock_sha256']},'independent_source_lock':ref(B/'source-lock.json'),
     'result':ref(B/'TERMINAL_VALIDATION.json'),'raw_execution_result':ref(root/'result.json'),
     'retained_original_aggregate_passed':False,'source_review':notes['scope_notes'][key],
     'owned_source_count':len(b['owned']),'owned_named_declarations':len(b['owned_declarations']),
     'owned_actual_theorem_kinds':br['actual_owned_kernel_theorem_count'],'complete_raw_public_types':br['literal_examples'],
     'full_scoped_kernel_checks':br['explicit_named_declarations'],'all_exact_kinds_kernel_axioms_and_private_actual_names_passed':True,
     'project_objects_reused':False,'pinned_external_objects_reused':True,'observed_axioms':br['observed_axioms'],
     'source_names_policy':'Every explicit named public/private/local declaration is checked by exact actual compiler identity/kind, genuine LeanCert kernel assertion and transitive axioms. Anonymous/generated helpers are compiled and covered transitively, not separately counted. Original same-named Challenge and Solution exports are checked in separate environments.',
     'complete_Target_and_canonical_scopes_distinguished_from_support':True,'original25_and10cleanpins_before_after_passed':True,
     'full_TR04_Target_proved':complete,'canonical_package_kernel_passed':key=='canonical_solution',
     'proof_source_changes':False,'authoritative_Linux_Comparator':False,
     'limits':'Local mathematical/kernel acceptance at the exact frozen205-input package only. Actual Linux Comparator acceptance, later descriptive/status edits and published promotion require separate exact-commit evidence. The old arbitrary-unfoldingRank tr04Statement is retained and not proved.' if complete else 'Only this separately frozen support scope is approved by this receipt. The complete Target is approved separately in the full_target/canonical_solution receipts; authoritative Linux/Comparator and publication remain separate.',
     'author_terminal_receipts':ref(B/'author-terminal-receipts.json'),'raw_literal_headers':ref(B/'raw-literal-header-check.json'),
     'canonical_input_review':ref(B/'canonical-input-review.json'),'challenge_negative_control':negative}
    p=B/('APPROVAL-'+key+'.json');p.write_text(json.dumps(approval,indent=2)+'\n');receipts.append(ref(p))
acceptance={'passed':True,'reviewer':'/root/recover_verification','proof_source_authorship':[],
 'recorded_utc':datetime.now(timezone.utc).isoformat(),'scope':'Complete unchanged original mathematical Target and frozen canonical package independently rebuilt and kernel checked, plus six separately scoped author blocks. No actual Linux/Comparator or published promotion acceptance.',
 'receipts':receipts,'result':ref(B/'TERMINAL_VALIDATION.json'),'raw_execution_result':ref(root/'result.json'),
 'retained_original_aggregate_passed':False,'raw_result_relabelled_or_rewritten':False,
 'terminal_aggregation_only_correction':ref(B/'canonical-replay-aggregation-correction.json'),
 'canonical_freeze':c['canonical_freeze'],'proof_commit':'027aaefbadf602ac460d0cf4cae7beed3181d712',
 'package_inputs':205,'fresh_Lean_producers':190,'proof_context_sources':188,'comparison_context_sources':2,
 'successful_source_build_and_positive_consumer_commands':197,'expected_Challenge_rejections':1,
 'total_kernel_commands':198,'distinct_proof_environment_named_kernel_identities':1821,'private_named_identities':180,'local_named_identities':1,
 'raw_complete_public_type_examples':80,'additional_expanded_Target_fixedProgram_and_Reviewed_identity_examples':3,
 'shared_exact_copies':184,'TR04_proof_modules':179,'selected_exports':['candidate_count_le_first_mode','cyclic_window_count_le_first_mode','NLA.TR04.target'],
 'observed_proof_axioms':['Classical.choice','Quot.sound','propext'],'project_objects_reused':False,'pinned_external_objects_reused':True,
 'retained_legacy_scaffold_claimed_proved':False,'comparison_placeholder_accepted_as_proof':False,
 'full_TR04_Target_proved':True,'canonical_package_kernel_passed':True,'authoritative_Linux_Comparator':False,'proof_source_changes':False,
 'evidence':{name:ref(B/name) for name in ['author-terminal-receipts.json','canonical-input-review.json','source-review-notes.json','global-inventory-correction.json','raw-literal-header-check.json','production-harness-proof-commit-binding.json','private-identity-controls/result.json','global-header-controls/result.json']},
 'reproducers':[ref(B/name) for name in ['prepare.py','prepare-canonical.py','source_inventory.py','replay-attempt-1.py','replay-corrected.py','make-corrected-replay.py','validate-terminal-raw-logs.py','make-canonical-replay.py','replay-shared-precanonical.py','check-private-identities.py','check-global-headers.py','check-author-terminal.py','check-canonical-inputs.py','check-raw-literal-headers.py','make-approval.py',*['integration-'+b['key']+'.lean.txt' for b in c['blocks']]]]}
retained=[B/name for name in ['source_inventory-before-global-fix.py','prepare-before-global-inventory-fix.py',
 'shared-source-lock-before-global-inventory-fix.json','check-author-terminal-attempt-1.py','author-terminal-check-diagnostic.json',
 'canonical-input-check-environment-diagnostic.json']]
retained.extend(p for p in sorted((B/'global-header-controls-attempt-1').iterdir()) if p.is_file())
acceptance['retained_preparation_diagnostics']=[ref(p) for p in retained]
acceptance['failed_global_fixture_accepted_as_canonical_proof']=False
acceptance['read_only_checker_preparation_failures_relabelled_as_proof_failures']=False
(B/'ACCEPTANCE.json').write_text(json.dumps(acceptance,indent=2)+'\n')
print(json.dumps({'passed':True,'acceptance_sha256':sha(B/'ACCEPTANCE.json'),'result_sha256':sha(root/'result.json'),'receipts':receipts},indent=2))
