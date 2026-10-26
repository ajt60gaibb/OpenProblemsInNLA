#!/usr/bin/env python3
"""Seal only the seven frozen deterministic RE05 support modules."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
B=Path(__file__).resolve().parent;REPO=B.parents[5];R=B/'run-attempt-2';artifacts={}
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
def bind(p,h=None):
    actual=sha(p)
    if h is not None:assert actual==h,str(p)
    artifacts[str(p.relative_to(REPO))]=actual;return actual
def read(p,h=None):bind(p,h);return json.loads(p.read_text())
c=read(B/'source-lock.json','c91bd6b8d968d71a69378ab5e626963d337c5de5171c753a43d5193e1354845a')
r=read(R/'result.json','1f5da34f7a92f6807afc36636602784dfe014b6277fe1ded1abbf812ad04f8ce')
assert r['passed'] and 'exception' not in r and len(r['commands'])==22
assert r['driver_sha256']==bind(B/'replay.py') and not r['project_objects_reused'] and r['private_objects_removed']
assert not r['full_RE05_Target_proved'] and not r['unconditional_SourceQueryBound_proved']
assert not r['probability_99of100_proved'] and not r['OriginalClaim_or_SourceCompanion_proved']
assert not r['Linux_or_Comparator_acceptance']
assert len(r['source_sha256'])==15 and len(c['owned_declarations'])==51
assert sum(x['kind'] in {'theorem','lemma'} for x in c['owned_declarations'])==41
assert len(c['declarations'])==162 and all(d['visibility']=='public' for d in c['declarations'])
for key in ['pins_before','pins_after']:assert len(r[key])==10 and all(x['clean'] for x in r[key])
for key in ['original18_before','original18_after']:assert len(r[key])==18 and all(x['passed'] for x in r[key])
assert r['TR04_before']['passed'] and r['TR04_after']['passed']
assert r['compiler_binary_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
assert '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in r['compiler']
for name,h in r['source_sha256'].items():
    bind(R/'sources'/name,h);bind(REPO/'lean-statements'/name,h)
for name,h in r['consumer_sha256'].items():bind(R/'sources'/name,h)
for cmd in r['commands']:
    assert cmd['exit_code']==cmd['expected_exit_code'];bind(R/cmd['log'],cmd['log_sha256'])
assert [(x['source'],x['exit_code']) for x in r['commands'] if x['exit_code']]==[('SorryControl.lean',1),('PrivateControl.lean',1),('TargetDefinitionControl.lean',1)]
assert len(r['negative_controls'])==3 and all(x['passed'] and not x['accepted_as_proof'] for x in r['negative_controls'].values())
old=read(B/'run-attempt-1/result.json','c1f5b115e62d7fd9f7bca6056d0e5aed07276d5e6cddfc51efef28fb98ad6445')
assert old['passed'] is False and len(old['commands'])==0
bind(B/'replay-attempt-1.py',old['driver_sha256']);read(B/'environment-precheck-diagnostic.json')
assert old['source_sha256']==r['source_sha256'] and old['consumer_sha256']==r['consumer_sha256']
notes=read(B/'SOURCE_REVIEW.json')
assert notes['all_seven_frozen_source_bodies_read_in_full'] and not notes['proof_source_authorship']
assert notes['new_explicit_names']==51 and notes['new_theorems']==41
for author in r['author_receipts']:
    data=read(REPO/author['path'],author['sha256']);assert data['passed'] and not data['project_objects_reused']
    lock=(REPO/author['path']).parent/'source-lock.json';bind(lock,data['source_lock_sha256'])
inputlock=read(REPO/c['input_lock']['path'],c['input_lock']['sha256'])
for rec in inputlock['source_inputs']:
    bind(REPO/rec['path'],rec['sha256']);bind(R/'preserved-inputs'/rec['path'],rec['sha256'])
headers=[]
for key,info in r['consumer_bindings'].items():
    assert len(info['literal_examples'])==r['blocks'][key]['complete_raw_theorem_types']
    for x in info['literal_examples']:
        assert re.fullmatch('[0-9a-f]{64}',x['verbatim_header_sha256']);headers.append(x)
assert len(headers)==41 and len({x['name'] for x in headers})==41
header_report={'passed':True,'raw_complete_public_type_count':41,'types':headers,'source_lock_sha256':sha(B/'source-lock.json'),'executed_driver_sha256':sha(B/'replay.py'),'all_types_compiled_in_fresh_positive_consumers':True}
(B/'RAW_HEADER_CHECK.json').write_text(json.dumps(header_report,indent=2)+'\n');bind(B/'RAW_HEADER_CHECK.json')
receipts=[]
for block in c['blocks']:
    key=block['key'];d=r['blocks'][key]
    assert d['passed'] and d['observed_axioms']==['Classical.choice','Quot.sound','propext']
    bind(REPO/block['author_freeze']['path'],block['author_freeze']['sha256'])
    report={'passed':True,'approval':'APPROVED_FROZEN_DETERMINISTIC_SUPPORT_SCOPE_ONLY','reviewer':'/root/recover_verification',
      'recorded_utc':datetime.now(timezone.utc).isoformat(),'scope_key':key,'author':block['author'],'proof_source_authorship':[],
      'owned_sources':block['owned'],'author_freeze':block['author_freeze'],'independent_source_lock_sha256':sha(B/'source-lock.json'),
      'result_path':str((R/'result.json').relative_to(REPO)),'result_sha256':sha(R/'result.json'),'checks':d,
      'source_review':notes['scope_notes'][key],'private_auxiliary_policy':notes['private_auxiliary_policy'],
      'all18_original_inputs_and10_clean_dependency_pins_before_after':True,'TR04_all205_inputs_unchanged':True,
      'raw_complete_public_types_compiled':d['complete_raw_theorem_types'],'negative_sorry_custom_private_axiom_and_Target_kind_controls_passed':True,
      'project_objects_reused':False,'only_pinned_external_package_objects_reused':True,'proof_source_or_original_ID_changes':False,
      'full_RE05_Target_proved':False,'probability_99of100_proved':False,'unconditional_SourceQueryBound_proved':False,
      'OriginalClaim_or_SourceCompanion_proved':False,'Linux_or_Comparator_acceptance':False}
    p=B/('APPROVAL-'+key+'.json');assert not p.exists();p.write_text(json.dumps(report,indent=2)+'\n')
    receipts.append({'path':str(p.relative_to(REPO)),'sha256':bind(p)})
for p in sorted(B.rglob('*')):
    if not p.is_file() or '__pycache__' in p.parts:continue
    assert p.suffix not in {'.olean','.ilean','.pyc'},str(p);bind(p)
out={'passed':True,'reviewer':'/root/recover_verification','recorded_utc':datetime.now(timezone.utc).isoformat(),
 'proof_source_authorship':[],'scope':'Seven frozen deterministic RE05 support modules only; four separately scoped approvals. Mutable spectral and later asymptotic/probability work are outside this snapshot.',
 'receipts':receipts,'source_lock_sha256':sha(B/'source-lock.json'),'fresh_result_sha256':sha(R/'result.json'),
 'fresh_project_producers':15,'positive_consumers':4,'expected_negative_rejections':3,'kernel_commands':22,
 'owned_source_modules':7,'owned_explicit_declarations':51,'owned_theorems':41,'owned_definitions':10,
 'distinct_named_closure_identities':162,'complete_raw_public_theorem_types':41,
 'observed_axioms':['Classical.choice','Quot.sound','propext'],'project_objects_reused':False,
 'private_objects_removed':True,'all18_original_inputs_unchanged':True,'all217_IDs_unchanged':True,'TR04_all205_inputs_unchanged':True,
 'initial_environment_precheck_accepted':False,'initial_environment_Lean_commands':0,
 'full_RE05_Target_proved':False,'probability_99of100_proved':False,'unconditional_SourceQueryBound_proved':False,
 'OriginalClaim_or_SourceCompanion_proved':False,'Linux_or_Comparator_acceptance':False,
 'artifact_hashes':artifacts}
p=B/'ACCEPTANCE.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'acceptance_sha256':sha(p),'result_sha256':sha(R/'result.json'),'receipts':receipts,'bound_artifacts':len(artifacts)},indent=2))
