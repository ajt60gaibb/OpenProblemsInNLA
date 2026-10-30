#!/usr/bin/env python3
"""Seal the two separately scoped actual gather/forward phase receipts."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5]
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'path':str(p.relative_to(REPO)),'sha256':sha(p)}
root=BASE/'run-attempt-1';r=json.loads((root/'result.json').read_text())
c=json.loads((BASE/'source-lock.json').read_text())
assert r['passed'] and r['project_sources']==115 and len(r['commands'])==117
assert len(r['declarations'])==1170 and len(r['private_or_local_named_declarations'])==53
assert r['driver_sha256']==sha(BASE/'replay.py') and r['inventory_sha256']==sha(BASE/'source_inventory.py')
assert r['source_lock_sha256']==sha(BASE/'source-lock.json') and r['private_name_provenance_sha256']==sha(BASE/'private-name-provenance.json')
assert r['lean_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
assert r['project_objects_reused'] is False and r['pinned_external_dependency_objects_reused']
assert all(v['passed'] for k in ['dependencies_before','dependencies_after','original25_before','original25_after'] for v in r[k])
assert all(r['source_unchanged_after'].values()) and all(r['author_locks_unchanged_after'].values())
for n,h in r['source_sha256'].items():assert sha(root/'sources'/n)==sha(REPO/'lean-statements'/n)==h
for n,h in r['consumer_sha256'].items():assert sha(root/'sources'/n)==h
for cmd in r['commands']:assert cmd['exit_code']==0 and sha(root/cmd['log'])==cmd['log_sha256']
history=json.loads((BASE/'author-history.json').read_text());assert history['passed']
assert not history['forward_interrupted_run_accepted'] and not history['forward_failed_development_consumer_accepted']
assert not history['negative_fixture_accepted_as_proof']
for n,h in history['artifact_hashes'].items():assert sha(REPO/n)==h
control=json.loads((BASE/'private-auditor-preflight/result.json').read_text())
assert control['passed'] and control['driver_sha256']==r['driver_sha256']
raw_headers=json.loads((BASE/'raw-literal-header-check.json').read_text())
assert raw_headers['passed'] and raw_headers['header_count']==81
assert raw_headers['driver_sha256']==r['driver_sha256'] and raw_headers['source_lock_sha256']==r['source_lock_sha256']
reviews={
 'candidate_gather':{
  'expected':(109,6,46,38,19),'approval':'APPROVED_FROZEN_ACTUAL_SELECTED_CANDIDATE_GATHER_PHASE_ONLY','extra':1,
  'notes':[
   'All six frozen source bodies were independently read. Literal code189..197 checks actual j<K, loads the seven live gather parameters and enters the installed bank40 after9 steps. The bank returns running at65; literal65/198..207 reaches metadata241 after11 more steps. The actual total is m*(11*q+7)+24, with the same additive CostThrough bound.',
   'The genuine gather embedding relates the actual caller memory/registers to FrameGatherParameters, with arbitrary scratch values. Its proved scalar trace preserves natural registers outside26..40 and real registers except6. The return writes only the stated metadata fields and preserves the exact TTCandidateProtectedNat set, including live candidate76 and allocation globals.',
   'For every legal ValidSVD and actual first-selection register relation, the candidate matrix is proved to equal explicitFirstFrames at the actual finite j. hcap establishes the actual width, the imported frame formula establishes parameter validity and injectivity, and actual stored U cells feed the real gather run. Child replies are not inputs to the frame construction.',
   'The concrete Layout endpoint derives separation for saved input,U,sigma,V from their fixed addresses and individual dimensions≤N, preserves their literal readbacks and every destination-exterior memory cell, proves exact metadata241 fields, and bounds actual charge by24*(N+1)^2. The caller still supplies the stated valid selection, stored arrays, dimension/address facts and j<K.',
   'All46 new explicit names, including19 private literal-code helpers and all27 author-selected public names, receive exact kind/kernel/axiom checks. All19 full public theorem headers are copied verbatim. An additional actual legal-trace consumer projects the running metadata endpoint, unchanged candidate76/allocation64/real0 and the charged bound.'
  ],
  'limits':'Selected candidate gather from actual label189 with the stated first-selection/readback/layout preconditions only. The j≥K exit, candidate repetition and whole recursive TT correctness/approximation/global cost/Target remain separate.'},
 'forward':{
  'expected':(68,4,76,62,62),'approval':'APPROVED_FROZEN_ACTUAL_FORWARD_CONTRACTION_AND_CALLER_RETURN_ONLY','extra':2,
  'notes':[
   'All four frozen source bodies were independently read. Literal instructions255..273 load the actual matrix caller registers and enter bank11 after19 steps. The caller relation uses actual frame/input/output/stride/dimension fields and arbitrary real scratch values. The matrix routine computes the actual tensor contraction from stored cells, without an evaluator or supplied result premise.',
   'The returned bank state is running at32. Tag0 takes the actual9-step first-buffer continuation; tag1 with the actual one/zero fields takes the actual11-step child-buffer continuation. The first selects the allocated workA/workB pointers; the child swaps current/next buffers. Both update previous rank, increment the actual level and branch to208 or286 according to actual level/order, stopping before the reverse decrement.',
   'Every legal trace/offset carries actual StoresTensor output=contract Q A, unchanged stored input and frame under literal memory separation, unchanged memory outside the computed output rectangle, and the stated outside-frame real/natural register sets. Metadata preservation is derived for any actually disjoint metadata block. No unstated capacity or free evaluation assumption was added.',
   'Actual charge is bounded by the incoming prefix plus19+17*(q+m+suffixSize+1)^3 and the actual9/11 scalar continuation steps. The forward tensor may be merged through the already-proved literal radix identity without executing a memory copy.',
   'All76 new explicit public names, including62 actual theorem constants, receive exact kind/kernel/axiom checks; every complete public theorem header is copied verbatim. Two additional consumers prove the actual terminal-level first return reaches running286 with stored contraction, and the actual child return swaps buffers and stores the radix-merged contraction with its charged bound.',
   'The author earlier syntax-only consumer failure and interrupted producer run remain retained and unaccepted. Only the separate full empty-object68-source+consumer author final replay is terminal evidence; this independent115-source batch uses its own empty object root.'
  ],
  'limits':'Actual forward setup, matrix call and first/child return under the explicit stored-data, separation, tag and register premises only. Establishing those premises at every recursive level, reversing/lifting, final error selection and the full TT Target/global cost remain separate.'}}
receipts=[]
for b in c['blocks']:
    key=b['key'];br=r['blocks'][key];v=reviews[key]
    actual=(br['project_closure_count'],br['owned_source_count'],len(br['owned_declarations']),br['actual_owned_kernel_theorem_count'],br['literal_examples'])
    assert actual==v['expected'],(key,actual)
    assert br['passed'] and br['all_named_declaration_checks_passed'] and br['actual_name_bindings_passed']
    assert br['observed_axioms']==['Classical.choice','Quot.sound','propext']
    assert sha(REPO/b['author_lock_path'])==b['author_lock_sha256']
    approval={'passed':True,'approval':v['approval'],'reviewer':'/root/recover_verification','proof_source_authorship':[],
     'recorded_utc':datetime.now(timezone.utc).isoformat(),'execution_started_utc':r['started_utc'],'execution_finished_utc':r['finished_utc'],
     'author':b['author'],'author_source_lock':{'path':b['author_lock_path'],'sha256':b['author_lock_sha256']},
     'independent_source_lock':ref(BASE/'source-lock.json'),'result':ref(root/'result.json'),'scoped_kernel_result':br,
     'source_review':v['notes'],'limits':v['limits'],'additional_actual_trace_examples':v['extra'],
     'project_objects_reused':False,'pinned_external_objects_reused':True,'observed_axioms':br['observed_axioms'],
     'source_names_policy':'Every explicit public/private/local source name is checked by actual compiler name/kind, genuine LeanCert kernel assertion and transitive axioms. Anonymous/generated helpers are covered by compilation and transitive axioms, not counted as separate explicit-name assertions.',
     'original25_and_clean10pins_before_after_passed':True,'author_history_and_auditor_controls':ref(BASE/'author-history.json'),'raw_literal_headers':ref(BASE/'raw-literal-header-check.json'),
     'proof_source_changes':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
    p=BASE/('APPROVAL-'+key+'.json');p.write_text(json.dumps(approval,indent=2)+'\n');receipts.append(ref(p))
accept={'passed':True,'reviewer':'/root/recover_verification','scope':'Two separately approved actual main phases; shared fresh closure only, no complete TT Target claim.',
 'recorded_utc':datetime.now(timezone.utc).isoformat(),'receipts':receipts,'result':ref(root/'result.json'),
 'fresh_project_sources':115,'successful_commands':117,'distinct_explicit_named_checks':1170,'explicit_private_named_checks':53,
 'new_sources':10,'new_explicit_names':122,'new_actual_theorem_kinds':100,'verbatim_public_type_examples':81,'additional_actual_trace_examples':3,
 'reproducers':[ref(BASE/name) for name in ['prepare.py','make-replay.py','replay.py','source_inventory.py','integration-candidate_gather.lean.txt','integration-forward.lean.txt','check-private-auditor.py','check-author-history.py','check-raw-literal-headers.py','make-approval.py']],
 'author_history':ref(BASE/'author-history.json'),'private_name_provenance':ref(BASE/'private-name-provenance.json'),
 'proof_source_changes':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
(BASE/'ACCEPTANCE.json').write_text(json.dumps(accept,indent=2)+'\n')
print(json.dumps({'passed':True,'acceptance_sha256':sha(BASE/'ACCEPTANCE.json'),'receipts':receipts,'result_sha256':sha(root/'result.json')},indent=2))
