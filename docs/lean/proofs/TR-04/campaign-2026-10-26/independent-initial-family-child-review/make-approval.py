#!/usr/bin/env python3
"""Seal separately scoped first-family and child-initialization receipts."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5]
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'path':str(p.relative_to(REPO)),'sha256':sha(p)}
root=BASE/'run-attempt-1';r=json.loads((root/'result.json').read_text());c=json.loads((BASE/'source-lock.json').read_text())
assert r['passed'] and r['project_sources']==123 and len(r['commands'])==125
assert len(r['declarations'])==1308 and len(r['private_or_local_named_declarations'])==118
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
assert not history['old_author_attempt_accepted'] and history['stopped_author_source_successes']==23
assert history['all118_frozen_source_records_and32_public_names_identical'] and not history['negative_fixture_accepted_as_proof']
for n,h in history['artifact_hashes'].items():assert sha(REPO/n)==h
control=json.loads((BASE/'private-auditor-preflight/result.json').read_text())
assert control['passed'] and control['driver_sha256']==r['driver_sha256']
raw=json.loads((BASE/'raw-literal-header-check.json').read_text())
assert raw['passed'] and raw['header_count']==51 and raw['driver_sha256']==r['driver_sha256']
assert raw['source_lock_sha256']==r['source_lock_sha256']
reviews={
 'initial_family':{
  'expected':(118,4,32,24,24),'approval':'APPROVED_FROZEN_ACTUAL_ORIGINAL_START_FIRST_EXPLICIT_FAMILY_AND_STAGE_PROTECTION_ONLY','extra':2,
  'notes':[
   'All four frozen bodies were independently read. The generic natural-destination invariant covers every Instruction case, ordinary and arbitrary full-SVD Step transitions and absorbing stopped states. The actual fixed program theorem decides the destination condition for all512 labels, proving actual natural0=original order throughout every legal trace.',
   'InitialMemory derives the original first-mode/suffix decomposition, exact stored original tensor in literal mixed-radix order and the first readMatrix view from unchanged InputMemory. It proves actual output-block safety from computed rows/cols and the concrete allocation, exact original first requested rank, positive-rank and minimum/cap register equalities; no caller-supplied decoded header or allocation is assumed at original Start.',
   'ttInitial_explicit_family composes the accepted original initializer, actual SVD167 and first-selection phase for every original positive-rank input/legal trace. The reply object is the actual arbitrary legal SVD tuple on that trace. At running189 it proves the exact explicit family relation, actual U/sigma/V readbacks, all17 allocation fields, candidate0 and positive count, original memory below firstU and actual prefix time/charge≤1024*(Size+1)^3.',
   'StageProtection defines explicit prior/input/response/frame/metadata/candidate regions and actual writable intervals. It derives their separation for level<order, monotonicity and protection of each own frame/metadata at the next level, concrete work-buffer and metadata write exclusion, and unchanged protected cells under arbitrary child writeSVD with dimensions≤N. Connecting every later runtime phase to these regions remains a caller/loop obligation.',
   'All32 new explicit names and all1243 explicit names in this scope receive exact kind/kernel/axiom checks, including private dependencies. Every one of24 full public theorem headers matches raw frozen bytes, including inline := by decide, and is independently applied. Additional consumers project the actual original Start→running189/candidate0<count/order/memory/cost endpoint and preserve any prior frame under an arbitrary later child full-SVD write.',
   'The original d537 author attempt remains stopped and unaccepted after23 producer successes, before a consumer. Its old generator, captured consumer, preflight failure and full118 source snapshots/log remain bound. Final c258 retains all118 source records and32 public names exactly and adds driver/consumer-input hash binding. Only its separate terminal119-command author result and this independent fresh125-command batch are accepted evidence.'
  ],
  'limits':'Original-input first-family phase and derived stage address protection only, with positive original requested ranks. No child iteration, reverse reconstruction, error/candidate selection, total full-program cost, approximation/Target or authoritative Linux/Comparator acceptance is claimed.'},
 'child_initialization':{
  'expected':(74,5,65,56,27),'approval':'APPROVED_FROZEN_ACTUAL_CHILD_HEADER_INITIALIZATION_TO_SVD237_ONLY','extra':1,
  'notes':[
   'All five frozen bodies were independently read. Literal controller208..236 actually reads the current mode header and requested-rank header and prepares a suffix-range call. Actual Single/range banks and finite tags4/5/6 return to214/222/230; min branches and frame-address arithmetic reach running child SVD237.',
   'The generic endpoint covers all natural header values, including zero. Actual rows are previousRank*mode, columns are the decoded suffix product, cap is min(requestedRank,min(rows,cols)), and frame is frames+level*square. The memory is unchanged and exactly TTChildKept natural registers are preserved. It does not assume a matrix evaluator, current tensor result, or predecoded values.',
   'The actual generic elapsed time and prefix charge are bounded by3*mode+3*rank+headerRangeTime+78. The original-input endpoint obtains literal mode/rank cells solely from the retained original header prefix, uses the actual allocation/order/level fields and reachable recursive format, and derives actual child dimensions, stepRank/frame and full StepBounds from Reachable rather than assuming capacity. It bounds elapsed and additive actual charge by100*(Size+1).',
   'The reachable-at endpoint expresses its head directly as the actual previous-rank register times the current mode. Positive original ranks and Reachable describe consistency of that head and its original suffix; the caller still must establish reachability/header/allocation/entry facts at each level. The source does not claim those loop facts or subsequent SVD/forward/reverse execution for free.',
   'All65 new explicit names, including29 private literal-code helpers and36 author-selected public names, receive exact kind/kernel/axiom checks; all925 explicit names in this scope are audited. All27 full public theorem headers match raw frozen bytes. A further actual legal-trace consumer supplies zero mode/rank headers and proves running237 with genuinely computed zero rows/cap, exact unchanged memory and the stated charge.'
  ],
  'limits':'Actual read-only child setup from208 through SVD entry237, with explicit actual header/entry premises; original capacity conclusions require the stated positive ranks, allocation and reachable format. Establishing these premises in every iteration and completing full TT execution/approximation/total cost/Target remain separate.'}}
receipts=[]
for b in c['blocks']:
    key=b['key'];br=r['blocks'][key];v=reviews[key]
    actual=(br['project_closure_count'],br['owned_source_count'],len(br['owned_declarations']),br['actual_owned_kernel_theorem_count'],br['literal_examples'])
    assert actual==v['expected'],(key,actual)
    assert br['passed'] and br['all_named_declaration_checks_passed'] and br['actual_name_bindings_passed']
    assert br['observed_axioms']==['Classical.choice','Quot.sound','propext']
    assert sha(REPO/b['author_lock_path'])==b['author_lock_sha256']
    out={'passed':True,'approval':v['approval'],'reviewer':'/root/recover_verification','proof_source_authorship':[],
     'recorded_utc':datetime.now(timezone.utc).isoformat(),'execution_started_utc':r['started_utc'],'execution_finished_utc':r['finished_utc'],
     'author':b['author'],'author_source_lock':{'path':b['author_lock_path'],'sha256':b['author_lock_sha256']},
     'independent_source_lock':ref(BASE/'source-lock.json'),'result':ref(root/'result.json'),'scoped_kernel_result':br,
     'source_review':v['notes'],'limits':v['limits'],'additional_actual_trace_examples':v['extra'],
     'raw_literal_headers':ref(BASE/'raw-literal-header-check.json'),'author_history_and_auditor_controls':ref(BASE/'author-history.json'),
     'source_names_policy':'All explicit public/private/local source names checked by exact actual compiler name/kind, genuine LeanCert kernel assertion and transitive axioms. Generated/anonymous helpers are kernel compiled and included transitively; no separate explicit-name assertion count claimed for them.',
     'project_objects_reused':False,'pinned_external_objects_reused':True,'original25_and_clean10pins_before_after_passed':True,
     'proof_source_changes':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
    q=BASE/('APPROVAL-'+key+'.json');q.write_text(json.dumps(out,indent=2)+'\n');receipts.append(ref(q))
accept={'passed':True,'reviewer':'/root/recover_verification','scope':'Two separately approved original first-family and child-initialization support phases; no whole TT Target claim.',
 'recorded_utc':datetime.now(timezone.utc).isoformat(),'receipts':receipts,'result':ref(root/'result.json'),
 'fresh_project_sources':123,'successful_commands':125,'distinct_explicit_named_checks':1308,'explicit_private_named_checks':118,
 'new_sources':9,'new_explicit_names':97,'new_actual_theorem_kinds':80,'verbatim_public_type_examples':51,'additional_actual_trace_examples':3,
 'reproducers':[ref(BASE/name) for name in ['prepare.py','make-replay.py','replay.py','source_inventory.py','integration-initial_family.lean.txt','integration-child_initialization.lean.txt','check-private-auditor.py','check-author-history.py','check-raw-literal-headers.py','make-approval.py']],
 'author_history':ref(BASE/'author-history.json'),'private_name_provenance':ref(BASE/'private-name-provenance.json'),
 'proof_source_changes':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
(BASE/'ACCEPTANCE.json').write_text(json.dumps(accept,indent=2)+'\n')
print(json.dumps({'passed':True,'acceptance_sha256':sha(BASE/'ACCEPTANCE.json'),'receipts':receipts,'result_sha256':sha(root/'result.json')},indent=2))
