#!/usr/bin/env python3
"""Seal separately scoped spectral/asymptotic and deterministic composition checks."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
B=Path(__file__).resolve().parent;REPO=B.parents[5];R=B/'run-attempt-1';artifacts={}
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
def bind(p,h=None):
    actual=sha(p)
    if h is not None:assert actual==h,str(p)
    artifacts[str(p.relative_to(REPO))]=actual;return actual
def read(p,h=None):bind(p,h);return json.loads(p.read_text())
c=read(B/'source-lock.json','83dc2842f53e84153052e91d7fb958f1e958af8844d20acfd5902b96eaf0238a')
r=read(R/'result.json','9db6740c3ffd58e41355970bd0e8f2662221c10bb5c40f718ce252933c94fa14')
assert r['passed'] and 'exception' not in r and len(r['commands'])==24
assert r['driver_sha256']==bind(B/'replay.py') and not r['project_objects_reused'] and r['private_objects_removed']
assert not r['full_RE05_Target_proved'] and r['unconditional_SourceQueryBound_proved'] and r['uniform_deterministic_QueryBound_proved']
assert not r['probability_99of100_proved'] and not r['OriginalClaim_or_SourceCompanion_proved'] and not r['Linux_or_Comparator_acceptance']
assert len(r['source_sha256'])==18 and len(c['owned_declarations'])==16
assert sum(x['kind'] in {'theorem','lemma'} for x in c['owned_declarations'])==15 and len(c['declarations'])==172
for key in ['pins_before','pins_after']:assert len(r[key])==10 and all(x['clean'] for x in r[key])
for key in ['original18_before','original18_after']:assert len(r[key])==18 and all(x['passed'] for x in r[key])
assert r['TR04_before']['passed'] and r['TR04_after']['passed']
assert r['compiler_binary_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
for name,h in r['source_sha256'].items():bind(R/'sources'/name,h);bind(REPO/'lean-statements'/name,h)
for name,h in r['consumer_sha256'].items():bind(R/'sources'/name,h)
for cmd in r['commands']:
    assert cmd['exit_code']==cmd['expected_exit_code'];bind(R/cmd['log'],cmd['log_sha256'])
assert [(x['source'],x['exit_code']) for x in r['commands'] if x['exit_code']]==[('SorryControl.lean',1),('PrivateControl.lean',1),('TargetDefinitionControl.lean',1)]
assert len(r['negative_controls'])==3 and all(x['passed'] and not x['accepted_as_proof'] for x in r['negative_controls'].values())
notes=read(B/'SOURCE_REVIEW.json');assert notes['all_four_frozen_source_bodies_and_expanded_consumers_read_in_full'] and not notes['proof_source_authorship']
for author in r['author_receipts']:
    data=read(REPO/author['path'],author['sha256']);assert data['passed'] and not data['project_objects_reused']
    bind((REPO/author['path']).parent/'source-lock.json',data['source_lock_sha256'])
inputs=read(REPO/c['input_lock']['path'],c['input_lock']['sha256'])
for x in inputs['source_inputs']:bind(REPO/x['path'],x['sha256']);bind(R/'preserved-inputs'/x['path'],x['sha256'])
prior=B.parent/'independent-deterministic-review'
previous=read(prior/'ACCEPTANCE.json','df155bba3d69cbc5aaa8dc5da108ddd7571ffd4664bd167aba92880bfe06026b')
previous_lock=read(prior/'source-lock.json','c91bd6b8d968d71a69378ab5e626963d337c5de5171c753a43d5193e1354845a')
assert previous['passed'] and previous['owned_source_modules']==7
for x in previous_lock['union']:bind(REPO/x['path'],x['sha256'])
headers=[x for info in r['consumer_bindings'].values() for x in info['literal_examples']]
assert len(headers)==15 and len({x['name'] for x in headers})==15
receipts=[]
for block in c['blocks']:
    key=block['key'];d=r['blocks'][key];assert d['passed'] and d['observed_axioms']==['Classical.choice','Quot.sound','propext']
    bind(REPO/block['author_freeze']['path'],block['author_freeze']['sha256'])
    out={'passed':True,'recorded_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/recover_verification','proof_source_authorship':[],
      'approval':'APPROVED_FROZEN_DETERMINISTIC_SUPPORT_SCOPE_ONLY','scope_key':key,'author':block['author'],
      'owned_sources':block['owned'],'author_freeze':block['author_freeze'],'source_review':notes['scope_notes'][key],
      'independent_source_lock_sha256':sha(B/'source-lock.json'),'result_sha256':sha(R/'result.json'),'checks':d,
      'project_objects_reused':False,'all18_originals_and10cleanpins_unchanged':True,'TR04_all205_unchanged':True,
      'unconditional_SourceQueryBound_proved':key=='spectral','standalone_asymptotic_bridge_retains_SourceQueryBound_premise':key=='asymptotic',
      'full_RE05_Target_proved':False,'probability_99of100_proved':False,'OriginalClaim_or_SourceCompanion_proved':False,
      'Linux_or_Comparator_acceptance':False,'proof_source_model_or_ID_changes':False}
    p=B/('APPROVAL-'+key+'.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');receipts.append({'path':str(p.relative_to(REPO)),'sha256':bind(p)})
composition=r['composed_deterministic_query_cap'];assert composition['passed'] and not composition['hcharge_or_hsource_premise']
out={'passed':True,'recorded_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/recover_verification',
 'scope':'Verification-consumer composition of independently reviewed production spectral and asymptotic endpoints into the original deterministic query cap only.',
 'production_proof_source_authorship':[],'verification_consumer_authorship':['RE05IndependentComposition.actual_query_cap','RE05IndependentComposition.uniform_deterministic_constants','RE05IndependentComposition.reviewed_Target_identity'],
 'composition':composition,'source_review':notes['composition_scope'],'fresh_result_sha256':sha(R/'result.json'),
 'full_RE05_Target_proved':False,'probability_99of100_proved':False,'OriginalClaim_or_SourceCompanion_proved':False,'Linux_or_Comparator_acceptance':False}
p=B/'APPROVAL-composition.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');receipts.append({'path':str(p.relative_to(REPO)),'sha256':bind(p)})
invocation={'argv':['python3','docs/lean/proofs/RE-05/campaign-2026-10-26/independent-query-bound-review/replay.py','--lean-bin','../tooling/lean-4.33.1-darwin_aarch64/bin','--package-cache','lean-statements/.lake/packages'],
 'driver_has_explicit_runtime_arguments':True,'default_object_parent':'Python tempfile.gettempdir()','executed_driver_sha256':r['driver_sha256'],
 'recorded_compiler_binary_SHA_guard_retained':True,'project_objects_reused':False}
(B/'INVOCATION.json').write_text(json.dumps(invocation,indent=2)+'\n')
for p in sorted(B.rglob('*')):
    if not p.is_file() or '__pycache__' in p.parts:continue
    assert p.suffix not in {'.olean','.ilean','.pyc'},str(p);bind(p)
out={'passed':True,'recorded_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/recover_verification','production_proof_source_authorship':[],
 'scope':'Four frozen deterministic RE05 spectral/asymptotic modules, plus an explicit original-query-cap verification composition. No probability or complete problem acceptance.',
 'receipts':receipts,'fresh_result_sha256':sha(R/'result.json'),'source_lock_sha256':sha(B/'source-lock.json'),
 'fresh_project_producers':18,'positive_consumers':3,'expected_negative_rejections':3,'kernel_commands':24,
 'owned_source_modules':4,'owned_named_declarations':16,'owned_theorems':15,'owned_definitions':1,
 'distinct_named_project_closure_identities':172,'complete_raw_public_type_checks':15,
 'extra_composition_kind_kernel_axiom_checks':3,'fixed_query_constants':{'C':1000000,'a':1,'b':1},
 'unconditional_SourceQueryBound_proved':True,'uniform_deterministic_QueryBound_proved':True,
 'full_RE05_Target_proved':False,'probability_99of100_proved':False,'OriginalClaim_or_SourceCompanion_proved':False,
 'Linux_or_Comparator_acceptance':False,'all18_originals_and217IDs_unchanged':True,'TR04_all205_unchanged':True,
 'previous_seven_frozen_sources_unchanged':True,'project_objects_reused':False,'private_objects_removed':True,
 'observed_axioms':['Classical.choice','Quot.sound','propext'],'artifact_hashes':artifacts}
p=B/'ACCEPTANCE.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'acceptance_sha256':sha(p),'result_sha256':sha(R/'result.json'),'receipts':receipts,'bound_artifacts':len(artifacts)},indent=2))
