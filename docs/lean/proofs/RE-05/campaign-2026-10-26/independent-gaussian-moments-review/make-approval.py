#!/usr/bin/env python3
"""Seal exact Gaussian scalar/private-helper support scope after terminal raw-log replay validation."""
from pathlib import Path
from datetime import datetime, timezone
import argparse,hashlib,json
B=Path(__file__).resolve().parent;REPO=B.parents[5];R=B/'run-attempt-2';artifacts={}
p=argparse.ArgumentParser();p.add_argument('--result-sha256',required=True);a=p.parse_args()
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
def bind(p,h=None):
    actual=sha(p)
    if h is not None:assert actual==h,str(p)
    artifacts[str(p.relative_to(REPO))]=actual;return actual
def read(p,h=None):bind(p,h);return json.loads(p.read_text())
c=read(B/'source-lock.json','ad96733b4910c27bf0f6397a700a5d25881f351b72ff8b0dbfde80624a3b928d')
r=read(R/'result.json',a.result_sha256)
assert r['passed'] and 'exception' not in r and len(r['commands'])==11
assert r['driver_sha256']==bind(B/'replay.py','94a73a5fcdf05314dc2e16282044c1ef1e8cf6aac3538a3f36db4bf5022d1e41')
assert not r['project_objects_reused'] and r['private_objects_removed']
for field in ['full_RE05_Target_proved','probability_99of100_proved','OriginalClaim_or_SourceCompanion_proved','Linux_or_Comparator_acceptance']:
    assert not r[field],field
assert len(r['source_sha256'])==7 and len(c['owned_declarations'])==11
assert all(d['kind']=='theorem' for d in c['owned_declarations'])
assert sum(d['visibility']=='public' for d in c['owned_declarations'])==7
assert sum(d['visibility']=='private' for d in c['owned_declarations'])==4
assert len(c['declarations'])==109
for key in ['pins_before','pins_after']:assert len(r[key])==10 and all(x['clean'] for x in r[key])
assert r['pins_before']==r['pins_after']
for key in ['original18_before','original18_after']:assert len(r[key])==18 and all(x['passed'] for x in r[key])
assert r['original18_before']==r['original18_after']
assert r['TR04_before']['passed'] and r['TR04_after']['passed']
assert r['compiler_binary_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
assert not Path(r['private_object_directory']).exists()
for name,h in r['source_sha256'].items():bind(R/'sources'/name,h);bind(REPO/'lean-statements'/name,h)
for name,h in r['consumer_sha256'].items():bind(R/'sources'/name,h)
for cmd in r['commands']:
    assert cmd['exit_code']==cmd['expected_exit_code'];bind(R/cmd['log'],cmd['log_sha256'])
assert [(x['source'],x['exit_code']) for x in r['commands'] if x['exit_code']]==[('SorryControl.lean',1),('PrivateControl.lean',1),('TargetDefinitionControl.lean',1)]
assert len(r['negative_controls'])==3 and all(x['passed'] and not x['accepted_as_proof'] for x in r['negative_controls'].values())
notes=read(B/'SOURCE_REVIEW.json');assert notes['all_frozen_source_public_private_bodies_and_expanded_consumer_read_in_full'] and not notes['proof_source_authorship']
for author in r['author_receipts']:
    data=read(REPO/author['path'],author['sha256']);assert data['passed'] and not data['project_objects_reused']
    bind((REPO/author['path']).parent/'source-lock.json',data['source_lock_sha256'])
inputs=read(REPO/c['input_lock']['path'],c['input_lock']['sha256'])
for x in inputs['source_inputs']:bind(REPO/x['path'],x['sha256']);bind(R/'preserved-inputs'/x['path'],x['sha256'])
previous=[]
for dirname,accept_hash,lock_hash in [
    ('independent-deterministic-review','df155bba3d69cbc5aaa8dc5da108ddd7571ffd4664bd167aba92880bfe06026b','c91bd6b8d968d71a69378ab5e626963d337c5de5171c753a43d5193e1354845a'),
    ('independent-query-bound-review','50d7c7efa1ab35a1c05caceb235b7b6f2c7fe3480a9d0b739e3e0824b8f8b25e','83dc2842f53e84153052e91d7fb958f1e958af8844d20acfd5902b96eaf0238a'),
    ('independent-median-review','3b4f801188b0b9e7b978dede02531a16bcd860e2cd609f1f244b0cb1e508b5a0','b6112ca3737e5ce1880aa902daaf9a5cca062305340de8a26a581872f6fe600e'),
    ('independent-spectral-split-review','a956f80cc6555c68bdf04d799efda88a93c7b580ecdf38a4dbc63b9f2ba55d75','ee1a8cd1c1d360dd9ac736b759386da7590addb5ac091f44daa5e278a8c1828d')]:
    prior=B.parent/dirname
    accepted=read(prior/'ACCEPTANCE.json',accept_hash);assert accepted['passed']
    locked=read(prior/'source-lock.json',lock_hash)
    for x in locked['union']:bind(REPO/x['path'],x['sha256'])
    previous.append({'path':str((prior/'ACCEPTANCE.json').relative_to(REPO)),'sha256':accept_hash,'all_frozen_production_sources_unchanged':True})

history=read(B/'AUTHOR_ATTEMPT_HISTORY.json');assert history['passed'] and not history['initial_author_acceptance']
for path,h in history['bound_artifacts'].items():bind(REPO/path,h)
failed=read(B/'run-attempt-1/result.json','5260fc029c9fa626746e0a6e5773007d99ef2c085c7c9baf770f24df791cb2ea')
assert not failed['passed'] and len(failed['commands'])==8
assert failed['source_sha256']==r['source_sha256'] and not Path(failed['private_object_directory']).exists()
old_headers=failed['consumer_bindings']['gaussian_moments']['literal_examples']
new_headers=r['consumer_bindings']['gaussian_moments']['literal_examples']
for old,new in zip(old_headers,new_headers,strict=True):
    for key in ['name','source','line','verbatim_header_sha256','application_arguments','application_name','visibility']:assert old[key]==new[key],key
assert sum(x['visibility']=='private' for x in new_headers)==4
assert all(x['application_name'].startswith('_private.NLA.Proofs.RE05.GaussianMoments.0.') and 'private_explicit%' in x['application_syntax'] for x in new_headers if x['visibility']=='private')
assert read(B/'GENERATOR_REPRODUCTION.json')['passed']

headers=[x for info in r['consumer_bindings'].values() for x in info['literal_examples']]
assert len(headers)==11 and len({x['name'] for x in headers})==11
block=c['blocks'][0];d=r['blocks']['gaussian_moments']
assert block['key']=='gaussian_moments' and d['passed'] and d['observed_axioms']==['Classical.choice','Quot.sound','propext']
assert d['closure_sources']==7 and d['explicit_named_kernel_checks']==109 and d['owned_named_declarations']==11 and d['complete_raw_theorem_types']==11
bind(REPO/block['author_freeze']['path'],block['author_freeze']['sha256'])
out={'passed':True,'recorded_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/recover_verification','proof_source_authorship':[],
    'approval':'APPROVED_FROZEN_GAUSSIAN_MOMENTS_SUPPORT_SCOPE_ONLY','scope_key':'gaussian_moments','author':block['author'],
    'owned_sources':block['owned'],'author_freeze':block['author_freeze'],'source_review':notes['scope_notes']['gaussian_moments'],
    'independent_source_lock_sha256':sha(B/'source-lock.json'),'result_sha256':sha(R/'result.json'),'checks':d,
    'exact_gaussianReal_0_1':True,'actual_stream_fourth_moment_3_consumer':True,'private_helpers_directly_and_transitively_checked':4,
    'project_objects_reused':False,'all18_originals_and10cleanpins_unchanged':True,'TR04_all205_unchanged':True,
    'full_RE05_Target_proved':False,'probability_99of100_proved':False,'OriginalClaim_or_SourceCompanion_proved':False,
    'Linux_or_Comparator_acceptance':False,'proof_source_model_or_ID_changes':False}
f=B/'APPROVAL-gaussian-moments.json';assert not f.exists();f.write_text(json.dumps(out,indent=2)+'\n')
receipt={'path':str(f.relative_to(REPO)),'sha256':bind(f)}
invocation={'argv':['python3','docs/lean/proofs/RE-05/campaign-2026-10-26/independent-gaussian-moments-review/replay.py','--lean-bin','../tooling/lean-4.33.1-darwin_aarch64/bin','--package-cache','lean-statements/.lake/packages','--run-dir','run-attempt-2'],
 'driver_has_explicit_runtime_arguments':True,'default_object_parent':'Python tempfile.gettempdir()','executed_driver_sha256':r['driver_sha256'],
 'recorded_compiler_binary_SHA_guard_retained':True,'project_objects_reused':False}
(B/'INVOCATION.json').write_text(json.dumps(invocation,indent=2)+'\n')
for f in sorted(B.rglob('*')):
    if not f.is_file() or '__pycache__' in f.parts:continue
    assert f.suffix not in {'.olean','.ilean','.pyc'},str(f);bind(f)
out={'passed':True,'recorded_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/recover_verification','production_proof_source_authorship':[],
 'scope':'One frozen RE05 standard Gaussian scalar and finite-product moment module, including all four private calculus helpers. No Wick, concentration, event-probability or complete problem acceptance.',
 'receipts':[receipt],'fresh_result_sha256':sha(R/'result.json'),'source_lock_sha256':sha(B/'source-lock.json'),
 'fresh_project_producers':7,'positive_consumers':1,'expected_negative_rejections':3,'kernel_commands':11,
 'owned_source_modules':1,'owned_named_declarations':11,'owned_theorems':11,'owned_definitions':0,
 'distinct_named_project_closure_identities':109,'complete_raw_public_type_checks':7,'complete_raw_private_type_checks':4,'owned_public_theorems':7,'owned_private_theorems':4,
 'exact_gaussianReal_0_1':True,'actual_stream_fourth_moment_3_consumer':True,'private_helpers_directly_and_transitively_checked':4,
 'full_RE05_Target_proved':False,'probability_99of100_proved':False,'OriginalClaim_or_SourceCompanion_proved':False,
 'Linux_or_Comparator_acceptance':False,'all18_originals_and217IDs_unchanged':True,'TR04_all205_unchanged':True,
 'previous_accepted_scopes':previous,'project_objects_reused':False,'private_objects_removed':True,
 'superseded_author_V1_accepted':False,'superseded_independent_attempt1_accepted':False,'raw_private_type_headers_unchanged_through_correction':True,
 'observed_axioms':['Classical.choice','Quot.sound','propext'],'artifact_hashes':artifacts}
f=B/'ACCEPTANCE.json';assert not f.exists();f.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'acceptance_sha256':sha(f),'result_sha256':sha(R/'result.json'),'receipt':receipt,'bound_artifacts':len(artifacts)},indent=2))
