#!/usr/bin/env python3
"""Seal the corrected fresh child scope while retaining the earlier failure."""
from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5]
PRIOR=BASE.parent/'independent-initial-family-child-review'
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'path':str(p.relative_to(REPO)),'sha256':sha(p)}
root=BASE/'run-attempt-1';rp=root/'result.json';r=json.loads(rp.read_text());c=json.loads((BASE/'source-lock.json').read_text())
b=c['blocks'][0];br=r['blocks']['child_initialization']
assert r['passed'] and r['project_sources']==74 and len(r['commands'])==75
assert len(r['declarations'])==925 and len(r['private_or_local_named_declarations'])==84
assert b['key']=='child_initialization' and len(b['owned_declarations'])==65 and len(b['author_selected_public_declarations'])==36
assert br['passed'] and br['all_named_declaration_checks_passed'] and br['actual_name_bindings_passed']
assert br['actual_owned_kernel_theorem_count']==56 and br['literal_examples']==27
assert br['observed_axioms']==['Classical.choice','Quot.sound','propext']
assert r['driver_sha256']==sha(BASE/'replay.py')==sha(PRIOR/'replay.py')
assert r['inventory_sha256']==sha(BASE/'source_inventory.py') and r['source_lock_sha256']==sha(BASE/'source-lock.json')
assert r['lean_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
assert not r['project_objects_reused'] and r['pinned_external_dependency_objects_reused']
assert all(v['passed'] for k in ['dependencies_before','dependencies_after','original25_before','original25_after'] for v in r[k])
assert all(r['source_unchanged_after'].values()) and all(r['author_locks_unchanged_after'].values())
for n,h in r['source_sha256'].items():assert sha(root/'sources'/n)==sha(REPO/'lean-statements'/n)==h
for n,h in r['consumer_sha256'].items():assert sha(root/'sources'/n)==h
for cmd in r['commands']:assert cmd['exit_code']==0 and sha(root/cmd['log'])==cmd['log_sha256']
old=json.loads((PRIOR/'run-attempt-1/result.json').read_text())
assert old['passed'] is False and old['blocks']['initial_family']['passed'] and not old['blocks']['child_initialization']['passed']
assert [(x['source'],x['exit_code']) for x in old['commands'] if x['exit_code']]==[('Independent_child_initialization_Consumer.lean',1)]
assert old['blocks']['child_initialization']['all_named_declaration_checks_passed']
assert old['blocks']['child_initialization']['actual_name_bindings_passed']
assert old['consumer_bindings']['child_initialization']['literal_examples']==r['consumer_bindings']['child_initialization']['literal_examples']
assert {n:h for n,h in old['source_sha256'].items() if n in r['source_sha256']}==r['source_sha256']
for cmd in old['commands']:assert sha(PRIOR/'run-attempt-1'/cmd['log'])==cmd['log_sha256']
for n,h in {**old['source_sha256'],**old['consumer_sha256']}.items():assert sha(PRIOR/'run-attempt-1/sources'/n)==h
old_extra=(PRIOR/'integration-child_initialization-attempt-1.lean.txt').read_text()
new_extra=(BASE/'integration-child_initialization.lean.txt').read_text()
assert old_extra.split(' := by',1)[0]==new_extra.split(' := by',1)[0]
assert new_extra==old_extra.replace('values hl hs had hmode hrank hvalues','values hl hs had (by simpa only [Nat.cast_zero] using hmode) (by simpa only [Nat.cast_zero] using hrank) hvalues')
control=json.loads((PRIOR/'private-auditor-preflight/result.json').read_text())
assert control['passed'] and control['driver_sha256']==r['driver_sha256']
assert control['custom_axiom_hidden_in_private_theorem_rejected'] and not control['negative_control_accepted_as_a_proof']
history=json.loads((PRIOR/'author-history.json').read_text());assert history['passed']
for n,h in history['artifact_hashes'].items():assert sha(REPO/n)==h
raw=json.loads((BASE/'raw-literal-header-check.json').read_text());assert raw['passed'] and raw['header_count']==27
assert raw['driver_sha256']==r['driver_sha256'] and raw['source_lock_sha256']==r['source_lock_sha256']
tree=ast.parse((PRIOR/'make-approval.py').read_text())
reviews=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='reviews' for t in n.targets))
v=reviews['child_initialization']
out={'passed':True,'approval':v['approval'],'reviewer':'/root/recover_verification','proof_source_authorship':[],
 'recorded_utc':datetime.now(timezone.utc).isoformat(),'execution_started_utc':r['started_utc'],'execution_finished_utc':r['finished_utc'],
 'author':b['author'],'author_source_lock':{'path':b['author_lock_path'],'sha256':b['author_lock_sha256']},
 'independent_source_lock':ref(BASE/'source-lock.json'),'result':ref(rp),'scoped_kernel_result':br,
 'source_review':v['notes'],'limits':v['limits'],'additional_actual_trace_examples':1,
 'raw_literal_headers':ref(BASE/'raw-literal-header-check.json'),'shared_identical_driver_controls':ref(PRIOR/'private-auditor-preflight/result.json'),
 'author_history_and_controls':ref(PRIOR/'author-history.json'),'retained_failed_batch':ref(PRIOR/'run-attempt-1/result.json'),
 'retained_consumer_diagnostic':ref(PRIOR/'zero-header-consumer-diagnostic.json'),
 'correction':'Only two proof arguments use Nat.cast_zero to transport the same zero-header premise; extra proposition, all27 literal types and frozen project sources unchanged.',
 'all74_prerequisite_sources_rebuilt_after_correction':True,'earlier_failed_consumer_accepted':False,
 'reproducers':[ref(BASE/n) for n in ['prepare.py','replay.py','source_inventory.py','integration-child_initialization.lean.txt','check-raw-literal-headers.py','make-approval.py']],
 'project_objects_reused':False,'pinned_external_objects_reused':True,'original25_and_clean10pins_before_after_passed':True,
 'proof_source_changes':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
(BASE/'APPROVAL.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'approval_sha256':sha(BASE/'APPROVAL.json'),'result_sha256':sha(rp)},indent=2))
