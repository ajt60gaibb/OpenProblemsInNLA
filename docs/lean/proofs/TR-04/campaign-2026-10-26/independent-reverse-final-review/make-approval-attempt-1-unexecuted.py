#!/usr/bin/env python3
"""Seal four scoped independent receipts only after the full replay passes."""
from pathlib import Path
from datetime import datetime,timezone
import collections,hashlib,json
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5]
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'path':str(p.relative_to(REPO)),'sha256':sha(p)}
root=BASE/'run-attempt-1';r=json.loads((root/'result.json').read_text())
c=json.loads((BASE/'source-lock.json').read_text())
reviews=json.loads((BASE/'source-review-notes.json').read_text())['blocks']
assert r['passed'] and r['project_sources']==103 and len(r['commands'])==107
assert len(r['declarations'])==1348 and len(r['private_or_local_named_declarations'])==128
assert r['driver_sha256']==sha(BASE/'replay.py') and r['inventory_sha256']==sha(BASE/'source_inventory.py')
assert r['source_lock_sha256']==sha(BASE/'source-lock.json') and r['private_name_provenance_sha256']==sha(BASE/'private-name-provenance.json')
assert r['lean_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
assert '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in r['lean_version']['stdout']
assert r['project_objects_reused'] is False and r['pinned_external_dependency_objects_reused']
assert all(v['passed'] for k in ['dependencies_before','dependencies_after','original25_before','original25_after'] for v in r[k])
assert all(r['source_unchanged_after'].values()) and all(r['author_locks_unchanged_after'].values())
for n,h in r['source_sha256'].items():assert sha(root/'sources'/n)==sha(REPO/'lean-statements'/n)==h
for n,h in r['consumer_sha256'].items():assert sha(root/'sources'/n)==h
for cmd in r['commands']:assert cmd['exit_code']==0 and sha(root/cmd['log'])==cmd['log_sha256']
history=json.loads((BASE/'author-history.json').read_text());assert history['passed']
assert not history['reverse_failed_development_consumer_accepted'] and not history['negative_fixture_accepted_as_proof']
assert len(history['terminal_author_results'])==4
for n,h in history['artifact_hashes'].items():assert sha(REPO/n)==h
control=json.loads((BASE/'private-identity-controls/result.json').read_text())
assert control['passed'] and control['driver_sha256']==r['driver_sha256']
assert control['two_modules_with_same_private_source_name_checked_distinctly']
assert control['hidden_custom_axiom_in_exact_second_module_rejected'] and not control['negative_control_accepted_as_proof']
assert control['wrong_module_rejected'] and control['wrong_actual_kind_rejected']
raw=json.loads((BASE/'raw-literal-header-check.json').read_text())
assert raw['passed'] and raw['header_count']==138
assert raw['driver_sha256']==r['driver_sha256'] and raw['source_lock_sha256']==r['source_lock_sha256']

# The same source spelling in two private modules is checked as twelve separate
# constants. The public/local identities remain unambiguous and no name is dropped.
private=[d for d in r['declarations'] if d['visibility']=='private']
counts=collections.Counter(d['name'] for d in private)
duplicates=sorted(n for n,k in counts.items() if k>1)
assert duplicates==['NLA.Proofs.TR04.code'+str(i) for i in range(349,355)]
assert all(counts[n]==2 for n in duplicates)
assert len({d['audit_id'] for d in r['declarations']})==1348
receipts=[]
for b in c['blocks']:
    key=b['key'];br=r['blocks'][key];v=reviews[key]
    actual=[br['project_closure_count'],br['owned_source_count'],len(br['owned_declarations']),br['actual_owned_kernel_theorem_count'],br['literal_examples']]
    assert actual==v['expected'],(key,actual)
    assert br['passed'] and br['all_named_declaration_checks_passed'] and br['actual_name_bindings_passed']
    assert br['observed_axioms']==['Classical.choice','Quot.sound','propext']
    assert sha(REPO/b['author_lock_path'])==b['author_lock_sha256']
    approval={'passed':True,'approval':v['approval'],'reviewer':'/root/recover_verification','proof_source_authorship':[],
     'recorded_utc':datetime.now(timezone.utc).isoformat(),'execution_started_utc':r['started_utc'],'execution_finished_utc':r['finished_utc'],
     'author':b['author'],'author_source_lock':{'path':b['author_lock_path'],'sha256':b['author_lock_sha256']},
     'independent_source_lock':ref(BASE/'source-lock.json'),'result':ref(root/'result.json'),'scoped_kernel_result':br,
     'source_review':v['notes'],'limits':v['limits'],'additional_actual_trace_examples':v['additional_actual_trace_examples'],
     'project_objects_reused':False,'pinned_external_objects_reused':True,'observed_axioms':br['observed_axioms'],
     'source_names_policy':'Every explicit public/private/local source name is checked by actual compiler name/kind, genuine LeanCert kernel assertion and transitive axioms. Private names are keyed by their exact module-qualified Lean kernel identity. Anonymous/generated helpers are compiled and covered transitively, not counted as separate explicit-name assertions.',
     'original25_and_clean10pins_before_after_passed':True,'author_history_and_auditor_controls':ref(BASE/'author-history.json'),
     'raw_literal_headers':ref(BASE/'raw-literal-header-check.json'),'private_identity_controls':ref(BASE/'private-identity-controls/result.json'),
     'proof_source_changes':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
    p=BASE/('APPROVAL-'+key+'.json');p.write_text(json.dumps(approval,indent=2)+'\n');receipts.append(ref(p))
reproducers=['prepare.py','make-replay.py','replay.py','source_inventory.py','check-private-identities.py','check-author-history.py',
 'check-raw-literal-headers.py','make-approval.py','source-review-notes.json','driver-provenance.json',
 *['integration-'+b['key']+'.lean.txt' for b in c['blocks']]]
acceptance={'passed':True,'reviewer':'/root/recover_verification',
 'scope':'Four separately approved actual final-copy/selector, direct349, reverse-level and child-SVD/stage-interface components. Shared fresh source closure only; no whole recursive TR04 Target claim.',
 'recorded_utc':datetime.now(timezone.utc).isoformat(),'receipts':receipts,'result':ref(root/'result.json'),
 'fresh_project_sources':103,'successful_commands':107,'distinct_explicit_kernel_identities_checked':1348,
 'distinct_source_user_names':len({d['name'] for d in r['declarations']}),
 'explicit_private_named_checks':127,'explicit_local_named_checks':1,
 'private_same_source_names_in_distinct_modules':duplicates,'all_private_actual_identities_checked_distinctly':True,
 'new_sources':14,'new_explicit_kernel_identities':219,'new_actual_theorem_kinds':181,
 'verbatim_public_type_examples':138,'additional_actual_trace_examples':6,
 'reproducers':[ref(BASE/name) for name in reproducers],'author_history':ref(BASE/'author-history.json'),
 'private_name_provenance':ref(BASE/'private-name-provenance.json'),'private_identity_controls':ref(BASE/'private-identity-controls/result.json'),
 'raw_literal_headers':ref(BASE/'raw-literal-header-check.json'),
 'proof_source_changes':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
(BASE/'ACCEPTANCE.json').write_text(json.dumps(acceptance,indent=2)+'\n')
print(json.dumps({'passed':True,'acceptance_sha256':sha(BASE/'ACCEPTANCE.json'),'receipts':receipts,'result_sha256':sha(root/'result.json')},indent=2))
