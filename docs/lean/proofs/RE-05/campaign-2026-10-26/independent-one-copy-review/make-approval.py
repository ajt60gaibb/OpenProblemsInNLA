#!/usr/bin/env python3
"""Seal deterministic one-copy support after independent terminal raw-log validation."""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import argparse,hashlib,json,re
B=Path(__file__).resolve().parent;REPO=B.parents[5];R=B/'run-attempt-1';artifacts={}
p=argparse.ArgumentParser();p.add_argument('--result-sha256',required=True);a=p.parse_args()
def sha(p):
 assert p.is_file() and not p.is_symlink(),str(p)
 return hashlib.sha256(p.read_bytes()).hexdigest()
def bind(p,h=None):
 got=sha(p)
 if h is not None:assert got==h,str(p)
 artifacts[str(p.relative_to(REPO))]=got;return got
def read(p,h=None):bind(p,h);return json.loads(p.read_text())
c=read(B/'source-lock.json','87d2f40656b9bed1a4025a39ec156d71e2d9da2fc36a058aa1dd66fb4a5509a3')
r=read(R/'result.json',a.result_sha256);assert r['passed'] and 'exception' not in r and len(r['commands'])==34
assert r['driver_sha256']==bind(B/'replay.py','35fabcc5d12dea1a4ea3a5853a64aa88a645150787de81a68a6a36266ee915fb')
assert len(c['union'])==30 and len(c['declarations'])==302 and len(c['owned_declarations'])==19
assert Counter(d['kind'] for d in c['owned_declarations'])=={'def':2,'theorem':17}
assert all(d['visibility']=='public' for d in c['owned_declarations'])
assert not r['project_objects_reused'] and r['private_objects_removed'] and not Path(r['private_object_directory']).exists()
assert r['compiler_binary_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
assert r['compiler_flags']==['-DautoImplicit=false']
for f in ['full_RE05_Target_proved','probability_99of100_proved','OriginalClaim_or_SourceCompanion_proved','Linux_or_Comparator_acceptance']:assert not r[f],f
for field in ['pins_before','pins_after']:assert len(r[field])==10 and all(x['clean'] for x in r[field])
assert r['pins_before']==r['pins_after'] and r['original18_before']==r['original18_after'] and len(r['original18_after'])==18
assert r['TR04_before']['passed'] and r['TR04_after']['passed']
for x in c['union']:
 rel=str(Path(x['path']).relative_to('lean-statements'));assert r['source_sha256'][rel]==x['sha256'];bind(REPO/x['path'],x['sha256']);bind(R/'sources'/rel,x['sha256'])
for n,h in r['consumer_sha256'].items():bind(R/'sources'/n,h)
for x in r['commands']:assert x['exit_code']==x['expected_exit_code'] and x['argv'][1]=='-DautoImplicit=false';bind(R/x['log'],x['log_sha256'])
assert [x['source'] for x in r['commands'][:30]]==[str(Path(x['path']).relative_to('lean-statements')) for x in c['union']]
assert [(x['source'],x['exit_code']) for x in r['commands'][30:]]==[('Independent_one_copy_Consumer.lean',0),('SorryControl.lean',1),('PrivateControl.lean',1),('TargetDefinitionControl.lean',1)]
b=c['blocks'][0];assert b['key']=='one_copy' and len(b['extra_consumer_theorems'])==5
expected=[(d['audit_id'],'theorem' if d['kind'] in {'theorem','lemma'} else 'inductive' if d['kind'] in {'inductive','structure'} else 'definition') for d in b['declarations']]+[(n,'theorem') for n in b['extra_consumer_theorems']]
actual=[(d['name'],d['audit_id'],d['visibility']) for d in b['declarations']]+[(n,n,'public') for n in b['extra_consumer_theorems']]
l=(R/r['commands'][30]['log']).read_text();assert sorted(re.findall(r'AUDITED_KIND (\S+) (\S+)',l))==sorted(expected)
assert sorted(re.findall(r'AUDITED_ACTUAL (\S+) (\S+) (\S+)',l))==sorted(actual)
axs=re.findall(r'AUDITED_AXIOMS (\S+) \[([^\]]*)\]',l);assert len(axs)==307 and sorted(n for n,_ in axs)==sorted(n for n,_ in expected)
assert all({v.strip() for v in vs.split(',') if v.strip()}<={'propext','Classical.choice','Quot.sound'} for _,vs in axs)
assert 'error:' not in l and 'sorryAx' not in l
for i,key in [(31,'sorry'),(32,'private_axiom'),(33,'kind')]:
 l=(R/r['commands'][i]['log']).read_text();assert l.count('error:')==1
 ax=re.findall(r'AUDITED_AXIOMS (\S+) \[([^\]]*)\]',l)
 if key=='kind':assert 'constant kind differs from frozen source' in l and not ax
 else:
  assert 'depends on sorry or unrecognized axioms' in l and len(ax)==1
  assert set(filter(None,(x.strip() for x in ax[0][1].split(','))))==({'sorryAx'} if key=='sorry' else {'_private.PrivateControl.0.RE05Negative.hiddenFalse'})
assert len(r['negative_controls'])==3 and all(x['passed'] and not x['accepted_as_proof'] for x in r['negative_controls'].values())
headers=r['consumer_bindings']['one_copy']['literal_examples'];assert len(headers)==17 and len({x['name'] for x in headers})==17
assert r['blocks']['one_copy']['passed'] and r['blocks']['one_copy']['explicit_named_kernel_checks']==307
notes=read(B/'SOURCE_REVIEW.json');assert notes['all_four_frozen_source_bodies_and_full_author_expanded_consumer_read_in_full'] and not notes['proof_source_authorship']
assert notes['explicit_lower_and_offset_events_retained'] and notes['zero_optimum_no_division']
freeze=read(REPO/b['author_freeze']['path'],b['author_freeze']['sha256']);assert len(freeze['new_sources'])==4
for ar in r['author_receipts']:assert read(REPO/ar['path'],ar['sha256'])['passed']
author=B.parent/'re05-one-copy-geometry'
for f in author.rglob('*'):
 if f.is_file() and '__pycache__' not in f.parts:
  if f.suffix in {'.olean','.ilean','.pyc'}:continue
  bind(f)
inputs=read(REPO/c['input_lock']['path'],c['input_lock']['sha256'])
for x in inputs['source_inputs']:bind(REPO/x['path'],x['sha256']);bind(R/'preserved-inputs'/x['path'],x['sha256'])
assert len(c['protected_RE05_proofs'])==27
for p,h in c['protected_RE05_proofs'].items():bind(REPO/p,h)
tr=read(REPO/'docs/lean/proofs/TR-04/campaign-2026-10-26/CANONICAL_PROMOTION_FREEZE_2026-10-26.json','44b5df77ea7ed70c35aac6e87b2001f2b6860a36f58f1156a50d01a3c83374f7')
for n,h in tr['inputs'].items():bind(REPO/tr['project']/n,h)
assert len(json.loads((REPO/'problem_ids.json').read_text()))==217;bind(REPO/'problem_ids.json')
approval={'passed':True,'recorded_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/recover_verification','proof_source_authorship':[],
 'approval':'APPROVED_FROZEN_DETERMINISTIC_ONE_COPY_SUPPORT_ONLY','author':b['author'],'author_freeze':b['author_freeze'],'owned_sources':b['owned'],
 'source_review_sha256':sha(B/'SOURCE_REVIEW.json'),'source_lock_sha256':sha(B/'source-lock.json'),'fresh_result_sha256':sha(R/'result.json'),
 'scope':notes['scope_notes']['one_copy'],'checks':r['blocks']['one_copy'],'explicit_lower_and_offset_events_retained':True,'analysis_optimum_before_all_plans':True,'zero_optimum_no_division':True,
 'full_RE05_Target_proved':False,'probability_99of100_proved':False,'OriginalClaim_or_SourceCompanion_proved':False,'Linux_or_Comparator_acceptance':False,'all18originals217IDs205TR04_and_prior27_RE05_sources_unchanged':True}
f=B/'APPROVAL-one-copy.json';assert not f.exists();f.write_text(json.dumps(approval,indent=2)+'\n');receipt={'path':str(f.relative_to(REPO)),'sha256':bind(f)}
for f in sorted(B.rglob('*')):
 if f.is_file() and '__pycache__' not in f.parts:
  assert f.suffix not in {'.olean','.ilean','.pyc'},str(f);bind(f)
accept={'passed':True,'recorded_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/recover_verification','proof_source_authorship':[],
 'scope':'Four deterministic same-plan original-output error modules; all explicit lower/offset events remain hypotheses. No event probability or complete problem acceptance.',
 'receipts':[receipt],'fresh_result_sha256':sha(R/'result.json'),'source_lock_sha256':sha(B/'source-lock.json'),'fresh_project_producers':30,'positive_consumers':1,'expected_negative_rejections':3,'kernel_commands':34,
 'owned_source_modules':4,'owned_named_declarations':19,'owned_theorems':17,'owned_definitions':2,'distinct_named_project_closure_identities':302,'kernel_declaration_assertions':307,'raw_type_checks':17,
 'project_objects_reused':False,'private_objects_removed':True,'observed_axioms':['Classical.choice','Quot.sound','propext'],
 'all18originals217IDs205TR04_and_prior27_RE05_sources_unchanged':True,'full_RE05_Target_proved':False,'probability_99of100_proved':False,'OriginalClaim_or_SourceCompanion_proved':False,'Linux_or_Comparator_acceptance':False,'artifact_hashes':artifacts}
f=B/'ACCEPTANCE.json';assert not f.exists();f.write_text(json.dumps(accept,indent=2)+'\n')
print(json.dumps({'passed':True,'result_sha256':sha(R/'result.json'),'approval':receipt,'acceptance_sha256':sha(f),'bound_artifacts':len(artifacts)},indent=2))
