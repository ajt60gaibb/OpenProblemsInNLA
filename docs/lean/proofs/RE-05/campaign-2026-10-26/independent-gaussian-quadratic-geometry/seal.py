#!/usr/bin/env python3
"""Seal independent exact GaussianQuadratic3 source and fresh-kernel scope."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
B=Path(__file__).resolve().parent;R=B/'run-attempt-1';REPO=B.parents[5];C=B.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
artifacts={}
def bind(p,h=None):
    assert p.is_file()and not p.is_symlink(),str(p)
    actual=sha(p)
    if h is not None:assert actual==h,str(p)
    artifacts[str(p.relative_to(REPO))]=actual
    return actual
def read(p,h=None):bind(p,h);return json.loads(p.read_text())
c=read(B/'source-lock.json','e76f658f20d1820c1cd7ed29dc47ccd0c78a985efe9d2a64045f474d8e7dd97b')
r=read(R/'result.json','6b726fd370948460a3e8ad752cc1f700ad1588ae8120c807e331423548b9efe7')
assert r['passed']and 'exception'not in r and len(r['commands'])==15
assert r['driver_sha256']==bind(B/'replay.py','1f7ecb522b450a5068f8c1ce61167d0b3ef5765b8c8ba550d510d7eb7b23de94')
assert not r['project_objects_reused']and r['private_objects_removed']
assert not Path(r['private_object_directory']).exists()
assert len(r['source_sha256'])==11 and len(c['owned_declarations'])==19
assert sum(d['kind']=='theorem'for d in c['owned_declarations'])==17
assert sum(d['kind']=='def'for d in c['owned_declarations'])==2
assert len(c['declarations'])==132 and sum(d['visibility']=='private'for d in c['declarations'])==4
for key in ['pins_before','pins_after']:assert len(r[key])==10 and all(x['clean']for x in r[key])
assert r['pins_before']==r['pins_after']
for key in ['original18_before','original18_after']:assert len(r[key])==18 and all(x['passed']for x in r[key])
assert r['original18_before']==r['original18_after']
assert r['TR04_before']['passed']and r['TR04_after']['passed']
assert r['compiler_binary_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
for n,h in r['source_sha256'].items():bind(R/'sources'/n,h);bind(REPO/'lean-statements'/n,h)
for n,h in r['consumer_sha256'].items():bind(R/'sources'/n,h)
for cmd in r['commands']:
    assert cmd['exit_code']==cmd['expected_exit_code'];bind(R/cmd['log'],cmd['log_sha256'])
assert [(x['source'],x['exit_code'])for x in r['commands']if x['exit_code']]==[('SorryControl.lean',1),('PrivateControl.lean',1),('TargetDefinitionControl.lean',1)]
assert len(r['negative_controls'])==3 and all(v['passed']and not v['accepted_as_proof']for v in r['negative_controls'].values())
checks=r['blocks']['quadratic'];assert checks['passed']and checks['closure_sources']==11
assert checks['explicit_named_kernel_checks']==132 and checks['owned_named_declarations']==19 and checks['complete_raw_theorem_types']==17
assert checks['observed_axioms']==['Classical.choice','Quot.sound','propext']
notes=read(B/'SOURCE_REVIEW.json','2a2fafcc0d87b00c6d2a9908dd2f5e1bffb324d6e62156b3770fa875040cd418')
assert notes['all_three_frozen_source_bodies_and17literal_theorem_types_read_in_full']and notes['no_mathematical_blocker']
assert not notes['reviewer_authored_owned_sources']
freeze=read(REPO/c['blocks'][0]['author_freeze']['path'],c['blocks'][0]['author_freeze']['sha256'])
for x in freeze['new_sources']+freeze['prerequisites']:bind(REPO/x['path'],x['sha256'])
author=read(C/'gaussian-quadratic-author-final/result.json','5e0cf3f534cd67121073e44adab3aa2c51325be8e5eafa5b609037aa4e5f676a')
assert author['passed']and not author['project_objects_reused']
bind(C/'gaussian-quadratic-author-final/source-lock.json',author['source_lock_sha256'])
bind(C/'GAUSSIAN_QUADRATIC_AUTHOR_RECEIPT.json','57793f2c9d85096cccdc07ccde1bf0a9d0857b856fc00a9e2767691dd4e43dcb')
inputs=read(REPO/c['input_lock']['path'],c['input_lock']['sha256'])
for x in inputs['source_inputs']:bind(REPO/x['path'],x['sha256']);bind(R/'preserved-inputs'/x['path'],x['sha256'])
assert len(json.loads((REPO/'problem_ids.json').read_text()))==217
preserved=[]
for name,h in [('re05-regression-geometry','053009446339025e52312c2da9d60b2c8b1f17c5bf5b219e7f0dcf507f3e0f22'),('re05-one-copy-geometry','8ebaa3281116cf13c0a945f531eaa250cd28b30689e329c123b428ca2929656c'),('re05-centered-offset-geometry','de22f4cd2054265fb2e2a7e1985f11798fc06a6d8b67803e282f8e6313b4aa52')]:
    f=read(C/name/'SOURCE_FREEZE.json',h)
    for x in f['new_sources']:bind(REPO/x['path'],x['sha256'])
    preserved.append(dict(path=str((C/name/'SOURCE_FREEZE.json').relative_to(REPO)),sha256=h,new_sources_unchanged=True))
for p in sorted(B.rglob('*')):
    if not p.is_file()or '__pycache__'in p.parts or p.name=='ACCEPTANCE.json'or p.name.startswith('seal-attempt-'):continue
    assert p.suffix not in {'.olean','.ilean','.pyc'},str(p);bind(p)
out=dict(passed=True,recorded_utc=datetime.now(timezone.utc).isoformat(),reviewer='/root/recover_geometry',author='/root',approval='APPROVED_FROZEN_ROOT_GAUSSIAN_QUADRATIC3_SCOPE_ONLY',source_approval_scope=c['source_approval_scope'],reviewer_authored_owned_sources=[],author_freeze=c['blocks'][0]['author_freeze'],source_lock_sha256=sha(B/'source-lock.json'),source_review_sha256=sha(B/'SOURCE_REVIEW.json'),fresh_result_sha256=sha(R/'result.json'),report_sha256=sha(B/'REPORT.md'),fresh_project_producers=11,positive_consumers=1,expected_negative_rejections=3,kernel_commands=15,owned_source_modules=3,owned_named_declarations=19,owned_theorems=17,owned_definitions=2,explicit_named_project_checks=132,private_prerequisite_checks=4,raw_literal_theorem_types=17,independent_edge_definition_and_theorem_assertions=7,observed_axioms=checks['observed_axioms'],project_objects_reused=False,private_objects_removed=True,all18_originals_and217IDs_unchanged=True,TR04_all205_unchanged=True,all10_clean_pins_unchanged=True,preserved_own_frozen_scopes=preserved,actual_iid_offset_variance_or_Markov_proved=False,full_RE05_Target_proved=False,probability_99percent_OriginalClaim_SourceCompanion_proved=False,Linux_Comparator_or_promotion_claim=False,artifact_hashes=artifacts)
p=B/'ACCEPTANCE.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(passed=True,acceptance_sha256=sha(p),result_sha256=sha(R/'result.json'),report_sha256=sha(B/'REPORT.md'),bound_artifacts=len(artifacts)),indent=2))
