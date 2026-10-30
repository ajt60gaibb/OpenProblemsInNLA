#!/usr/bin/env python3
"""Build immutable cumulative metadata for six separately accepted RE05 support audits."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
B=Path(__file__).resolve().parent;REPO=B.parents[5];C=B.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
TABLE=[
 ('independent-deterministic-review','df155bba3d69cbc5aaa8dc5da108ddd7571ffd4664bd167aba92880bfe06026b','run-attempt-2',22,7),
 ('independent-query-bound-review','50d7c7efa1ab35a1c05caceb235b7b6f2c7fe3480a9d0b739e3e0824b8f8b25e','run-attempt-1',24,4),
 ('independent-median-review','3b4f801188b0b9e7b978dede02531a16bcd860e2cd609f1f244b0cb1e508b5a0','run-attempt-1',14,2),
 ('independent-spectral-split-review','a956f80cc6555c68bdf04d799efda88a93c7b580ecdf38a4dbc63b9f2ba55d75','run-attempt-1',26,5),
 ('independent-gaussian-moments-review','33454968fdffe4f45234641a3c1d19e6b58998c152744c1ed137f96db9cdb05e','run-attempt-2',11,1),
 ('independent-gaussian-wick-review','ce2a4bc2fcbbca28cefc44adc7c4078a7839347d11aa0f8e48c65891097ae55c','run-attempt-1',12,1)]
assert not (B/'ACCEPTANCE_INDEX.json').exists()
artifacts={};queue=[];skipped=set()
def bind(p,h=None):
 p=Path(p)
 if not p.is_absolute():p=REPO/p
 assert p.is_file() and not p.is_symlink(),str(p)
 rel=str(p.relative_to(REPO));assert not any(x in p.parts for x in ['__pycache__'])
 assert p.suffix not in {'.olean','.ilean','.pyc'},rel
 actual=sha(p)
 if h is not None:assert actual==h,(rel,actual,h)
 if rel in artifacts:assert artifacts[rel]==actual
 else:artifacts[rel]=actual;queue.append(p)
 return {'path':rel,'sha256':actual}
def read(p,h=None):rec=bind(p,h);return json.loads((REPO/rec['path']).read_text())
def walk(folder):
 for p in sorted(folder.rglob('*')):
  if p.is_symlink() or '__pycache__' in p.parts or 'objects' in p.parts or '.lake' in p.parts or p.suffix in {'.olean','.ilean','.pyc'}:continue
  if p.is_file():bind(p)
scopes=[]
for name,h,run,count,modules in TABLE:
 root=C/name;a=read(root/'ACCEPTANCE.json',h);r=read(root/run/'result.json',a['fresh_result_sha256']);cfg=read(root/'source-lock.json',a['source_lock_sha256'])
 assert a['passed'] and r['passed'] and len(r['commands'])==count and not r['project_objects_reused']
 assert not r['full_RE05_Target_proved'] and not r['probability_99of100_proved']
 for path,digest in a['artifact_hashes'].items():bind(REPO/path,digest)
 walk(root)
 scopes.append({'directory':str(root.relative_to(REPO)),'acceptance':bind(root/'ACCEPTANCE.json',h),'source_lock':bind(root/'source-lock.json'),
  'result':bind(root/run/'result.json'),'run_directory':run,'separately_fresh_project_producers':len(cfg['union']),
  'positive_consumer_count':len(r['commands'])-len(cfg['union'])-3,'expected_negative_controls':3,'actual_kernel_commands':count,
  'owned_modules':modules,'started_utc':r['started_utc'],'finished_utc':r['finished_utc'],
  'portable_replay_directory':str((C/('independent-deterministic-portable' if modules==7 else name)).relative_to(REPO)),
  'proof_source_authorship':[]})
checkpoints=[];historical_differences=[]
for p in sorted(C.glob('ACCEPTED_*CHECKPOINT.json')):
 ref=subprocess.check_output(['git','log','-1','--format=%H','--',str(p.relative_to(REPO))],cwd=REPO,text=True).strip();assert re.fullmatch('[0-9a-f]{40}',ref),p
 rec=bind(p);d=json.loads(p.read_text());assert subprocess.check_output(['git','show',ref+':'+rec['path']],cwd=REPO)==p.read_bytes()
 for path,h in d['file_sha256'].items():
  q=REPO/path
  if q.is_file() and not q.is_symlink() and sha(q)==h:bind(q,h)
  else:historical_differences.append({'checkpoint':rec['path'],'git_ref':ref,'path':path,'sha256':h,'current_path_hash_is_not_substituted':True})
 checkpoints.append({**rec,'immutable_git_ref':ref,'historical_file_count':len(d['file_sha256']),'historical_TR04_count':len(d['TR04_canonical205_sha256'])})
assert len(checkpoints)==6
# Author replay inputs, full raw logs and source snapshots; compiled outputs/cache links are excluded.
for name in ['prerequisites-author','orthogonal-optimum-author','re05-orthonormal-geometry','query-count-author','re05-spectral-geometry','query-asymptotic-algebra','median-author','re05-spectral-split-geometry','gaussian-moments-author','gaussian-moments-author-v2','gaussian-wick-author','independent-deterministic-portable','independent-accepted-thirteen-wiring-review']:
 assert (C/name).is_dir(),name
 walk(C/name)
# Resolve hash-bearing JSON artifact references. Historical checkpoint maps retain their own Git contexts.
checkpoint_paths={x['path'] for x in checkpoints}
def resolve(parent,value):
 if not value or '\n' in value or '\x00' in value or ':' in value:return None
 p=Path(value)
 candidates=[p] if p.is_absolute() else [parent/p,REPO/p]
 for p in candidates:
  try:
   rel=p.relative_to(REPO)
   if '..' in rel.parts:continue
   ordinary=p.is_file() and not p.is_symlink()
  except (ValueError,OSError):continue
  if ordinary and not any(x in p.parts for x in ['objects','.lake','__pycache__']) and p.suffix not in {'.olean','.ilean','.pyc'}:return p
 return None
def refs(d,parent):
 if isinstance(d,dict):
  if isinstance(d.get('path'),str) and re.fullmatch('[0-9a-f]{64}',str(d.get('sha256',''))):
   p=resolve(parent,d['path'])
   if p:bind(p,d['sha256'])
  for k,v in d.items():
   if isinstance(k,str) and '/' in k and isinstance(v,str) and re.fullmatch('[0-9a-f]{64}',v):
    p=resolve(parent,k)
    if p:bind(p,v)
   refs(v,parent)
 elif isinstance(d,list):
  for v in d:refs(v,parent)
while queue:
 p=queue.pop(0)
 if p.suffix=='.json' and p.is_relative_to(C) and str(p.relative_to(REPO)) not in checkpoint_paths:
  try:d=json.loads(p.read_text())
  except (ValueError,UnicodeDecodeError):continue
  refs(d,p.parent)
freeze=read(REPO/'docs/lean/proofs/TR-04/campaign-2026-10-26/CANONICAL_PROMOTION_FREEZE_2026-10-26.json','44b5df77ea7ed70c35aac6e87b2001f2b6860a36f58f1156a50d01a3c83374f7')
canonical={str(Path(freeze['project'])/p):h for p,h in freeze['inputs'].items()};assert len(canonical)==205
for p,h in canonical.items():bind(REPO/p,h)
original=read(C/'attained-input-lock.json','05d6b0bc8a3fd4dc65facb3144a50d9dc51bf0a1dd57e04d0c522213415e597d')
for x in original['source_inputs']:bind(REPO/x['path'],x['sha256'])
census=read(B/'SOURCE_CENSUS.json');assert len(census['RE05_modules'])==20 and census['RE05_explicit_named_declarations']==156
for p in ['AGGREGATE_WIRING_REVIEW.json','before-Proofs.lean.txt','after-Proofs.lean.txt','build-index.py','build-index-attempt-1.py','build-index-attempt-2.py','BUILD_DIAGNOSTIC.json','verify-index.py','README.md']:bind(B/p)
wiring=json.loads((B/'AGGREGATE_WIRING_REVIEW.json').read_text());bind(REPO/wiring['file'],wiring['after_sha256'])
assert len(json.loads((REPO/'problem_ids.json').read_text()))==217
failures=[]
for name,path,count in [
 ('independent_environment_precheck','independent-deterministic-review/run-attempt-1/result.json',0),
 ('author_stream_consumer_V1','gaussian-moments-author/result.json',8),
 ('independent_private_name_syntax_attempt1','independent-gaussian-moments-review/run-attempt-1/result.json',8)]:
 p=C/path;d=read(p);assert not d['passed'] and len(d['commands'])==count
 failures.append({**bind(p),'label':name,'actual_commands':count,'accepted':False})

out={'recorded_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/recover_verification','production_proof_source_authorship':[],
 'scope':'Twenty separately accepted RE05 support modules and six immutable independent fresh audit receipts. Partial deterministic/moment support only.',
 'source_census':bind(B/'SOURCE_CENSUS.json'),'modules':20,'explicit_RE05_named_declarations':156,'RE05_definitions':24,'RE05_theorems':132,'RE05_public_names':152,'RE05_private_names':4,
 'audited_project_source_union':28,'audited_explicit_project_name_union':267,'aggregate_import_source_closure':27,
 'independent_fresh_runs':scopes,'number_of_independent_fresh_runs':6,'sum_of_separate_run_commands':109,'single_combined_109_command_run_performed':False,
 'sum_of_separate_producer_commands':80,'sum_of_separate_positive_consumer_commands':11,'sum_of_separate_expected_negative_rejections':18,
 'observed_positive_axiom_union':['Classical.choice','Quot.sound','propext'],'original18_lock':bind(C/'attained-input-lock.json'),'permanent_IDs':217,
 'TR04_canonical205_sha256':canonical,'historical_checkpoints':checkpoints,'historical_context_differences':historical_differences,
 'aggregate_wiring_review':bind(B/'AGGREGATE_WIRING_REVIEW.json'),'current_aggregate_sha256':wiring['after_sha256'],
 'retained_failures':failures,'retained_failure_policy':'Initial environment-precheck failure, author Gaussian consumer V1 failure and independent private-name consumer attempt1 failure remain false, retained and excluded from accepted runs. Earlier development diagnostics remain historical.',
 'compiler_policy':'Exact official Lean4.33.1 Darwin binary/commit retained; independent replays take explicit runtime paths (first-seven uses separately hash-checked portable wrapper). External ten pinned package caches only; no project objects reused.',
 'complete_RE05_Target_proved':False,'actual_copy_success_probability_proved':False,'OriginalClaim_or_SourceCompanion_proved':False,'new_Linux_or_Comparator_acceptance':False,'new_kernel_commands_for_this_index':0,
 'problem_status':'Solved; unchanged','mutable_Quadratic_Regression_GT_vendor_and_later_work_excluded':True,'artifact_sha256':dict(sorted(artifacts.items()))}
(B/'ACCEPTANCE_INDEX.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'index_sha256':sha(B/'ACCEPTANCE_INDEX.json'),'bound_artifacts':len(artifacts),'historical_context_differences':historical_differences,'scoped_runs':6,'command_sum':109},indent=2))
