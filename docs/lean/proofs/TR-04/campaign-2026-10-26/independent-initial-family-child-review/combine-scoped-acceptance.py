#!/usr/bin/env python3
"""Combine a passed first-family block with the corrected separate child replay."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5]
CHILD=BASE.parent/'independent-child-initialization-review'
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'path':str(p.relative_to(REPO)),'sha256':sha(p)}
a=BASE/'APPROVAL-initial_family-v2.json';b=CHILD/'APPROVAL.json'
assert sha(a)=='d2d4acb86933d9566493df98772683a13ea1590e0308072123b40b2260a65a94'
x=json.loads(a.read_text());y=json.loads(b.read_text())
assert x['passed'] and y['passed'] and x['aggregate_batch_passed'] is False
assert not x['failed_child_counterpart_accepted'] and not y['earlier_failed_consumer_accepted']
old=json.loads((BASE/'run-attempt-1/result.json').read_text())
new=json.loads((CHILD/'run-attempt-1/result.json').read_text())
assert old['passed'] is False and old['blocks']['initial_family']['passed']
assert new['passed'] and len(new['commands'])==75
assert sha(BASE/'replay.py')==sha(CHILD/'replay.py')==old['driver_sha256']==new['driver_sha256']
assert {k:v for k,v in old['source_sha256'].items() if k in new['source_sha256']}==new['source_sha256']
assert old['consumer_bindings']['child_initialization']['literal_examples']==new['consumer_bindings']['child_initialization']['literal_examples']
for name,h in old['source_sha256'].items():assert sha(REPO/'lean-statements'/name)==h
assert len(old['source_sha256'])==123
for p,d in [(a,x),(b,y)]:
    assert d['reviewer']=='/root/recover_verification' and not d['proof_source_authorship']
    assert not d['full_TR04_Target_proved'] and not d['authoritative_Linux_Comparator']
    rr=d.get('result',d.get('retained_partial_batch_result'));assert sha(REPO/rr['path'])==rr['sha256']
out={'passed':True,'reviewer':'/root/recover_verification','recorded_utc':datetime.now(timezone.utc).isoformat(),
 'scope':'Two separately approved support scopes. Initial-family uses its complete passed block from a false aggregate; child uses a separate entirely fresh corrected74-source replay.',
 'receipts':[ref(a),ref(b)],'distinct_project_sources_covered':123,'new_frozen_sources':9,'new_explicit_names':97,'new_actual_theorem_kinds':80,
 'successful_fresh_scope_commands':{'initial_family':119,'child_initialization':75},'verbatim_public_type_examples':51,'additional_actual_trace_examples':3,
 'retained_aggregate_result':ref(BASE/'run-attempt-1/result.json'),'retained_aggregate_run_passed':False,
 'corrected_child_result':ref(CHILD/'run-attempt-1/result.json'),'old_child_consumer_failure_accepted':False,
 'unexecuted_full_aggregate_approval_template_accepted':False,
 'prior_scoped_description_receipt':ref(BASE/'APPROVAL-initial_family.json'),
 'reproducers':[ref(p) for p in [BASE/'approve-initial-family.py',BASE/'clarify-initial-family-scope.py',BASE/'combine-scoped-acceptance.py',CHILD/'prepare.py',CHILD/'replay.py',CHILD/'make-approval.py',CHILD/'check-raw-literal-headers.py']],
 'proof_inputs_changed':False,'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
(BASE/'TWO_SCOPE_ACCEPTANCE.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'acceptance_sha256':sha(BASE/'TWO_SCOPE_ACCEPTANCE.json'),'retained_aggregate_run_passed':False},indent=2))
