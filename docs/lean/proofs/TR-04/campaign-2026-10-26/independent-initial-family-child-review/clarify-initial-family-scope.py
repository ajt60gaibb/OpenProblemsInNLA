#!/usr/bin/env python3
"""Seal only the terminal initial-family scope in an otherwise failed batch."""
from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5]
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'path':str(p.relative_to(REPO)),'sha256':sha(p)}
root=BASE/'run-attempt-1';rp=root/'result.json';r=json.loads(rp.read_text())
c=json.loads((BASE/'source-lock.json').read_text());b=c['blocks'][0];br=r['blocks']['initial_family']
assert b['key']=='initial_family' and r['passed'] is False and br['passed']
assert len(r['commands'])==125 and r['project_sources']==123
assert [(x['source'],x['exit_code']) for x in r['commands'] if x['exit_code']]==[('Independent_child_initialization_Consumer.lean',1)]
assert br['project_closure_count']==118 and br['owned_source_count']==4 and len(br['owned_declarations'])==32
assert br['explicit_named_declarations']==1243 and br['actual_owned_kernel_theorem_count']==24 and br['literal_examples']==24
assert br['all_named_declaration_checks_passed'] and br['actual_name_bindings_passed']
assert br['observed_axioms']==['Classical.choice','Quot.sound','propext']
assert r['driver_sha256']==sha(BASE/'replay.py') and r['inventory_sha256']==sha(BASE/'source_inventory.py')
assert r['source_lock_sha256']==sha(BASE/'source-lock.json')
assert r['lean_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
assert not r['project_objects_reused'] and r['pinned_external_dependency_objects_reused']
assert all(v['passed'] for k in ['dependencies_before','dependencies_after','original25_before','original25_after'] for v in r[k])
assert all(r['source_unchanged_after'].values()) and all(r['author_locks_unchanged_after'].values())
for n,h in r['source_sha256'].items():assert sha(root/'sources'/n)==sha(REPO/'lean-statements'/n)==h
for n,h in r['consumer_sha256'].items():assert sha(root/'sources'/n)==h
for cmd in r['commands']:assert sha(root/cmd['log'])==cmd['log_sha256']
history=json.loads((BASE/'author-history.json').read_text());assert history['passed'] and not history['old_author_attempt_accepted']
for n,h in history['artifact_hashes'].items():assert sha(REPO/n)==h
raw=json.loads((BASE/'raw-literal-header-check.json').read_text());assert raw['passed'] and raw['header_count']==51
assert raw['driver_sha256']==r['driver_sha256']
tree=ast.parse((BASE/'make-approval.py').read_text())
reviews=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='reviews' for t in n.targets))
v=reviews['initial_family']
out={'passed':True,'approval':v['approval'],'reviewer':'/root/recover_verification','proof_source_authorship':[],
 'recorded_utc':datetime.now(timezone.utc).isoformat(),'execution_started_utc':r['started_utc'],'execution_finished_utc':r['finished_utc'],
 'author':b['author'],'author_source_lock':{'path':b['author_lock_path'],'sha256':b['author_lock_sha256']},
 'independent_source_lock':ref(BASE/'source-lock.json'),'retained_partial_batch_result':ref(rp),
 'aggregate_batch_passed':False,'scoped_kernel_result':br,'fresh_scope_sources':118,'fresh_scope_commands_including_consumer':119,
 'source_review':[note.replace('Only its separate terminal119-command author result and this independent fresh125-command batch are accepted evidence.', 'Only the terminal119-command author result and the complete118-source/consumer119 initial-family block of the independent batch are accepted for this scope; the child consumer failure leaves the aggregate125-command result false.') for note in v['notes']],'limits':v['limits'],'additional_actual_trace_examples':2,
 'raw_literal_headers':ref(BASE/'raw-literal-header-check.json'),'author_history_and_auditor_controls':ref(BASE/'author-history.json'),
 'prior_scoped_receipt':ref(BASE/'APPROVAL-initial_family.json'),'description_clarification':'Clarify the final review sentence: only the first-family block passes; the125-command aggregate remains false. No mathematical finding, source, statement, command or acceptance scope changes.','failed_child_counterpart_accepted':False,'retained_child_consumer_diagnostic':ref(BASE/'zero-header-consumer-diagnostic.json'),
 'project_objects_reused':False,'pinned_external_objects_reused':True,'original25_and_clean10pins_before_after_passed':True,
 'proof_source_changes':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
(BASE/'APPROVAL-initial_family-v2.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'approval_sha256':sha(BASE/'APPROVAL-initial_family-v2.json'),'aggregate_batch_passed':False,'result_sha256':sha(rp)},indent=2))
