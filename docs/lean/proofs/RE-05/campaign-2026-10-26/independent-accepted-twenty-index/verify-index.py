#!/usr/bin/env python3
"""Read-only hash, historical-Git-context and raw-log validator; executes no Lean/shell payloads."""
from pathlib import Path
import argparse,atexit,hashlib,json,re,subprocess
B=Path(__file__).resolve().parent;REPO=B.parents[5]
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--git-ref');p.add_argument('--report',type=Path);a=p.parse_args()
blob=None;trees={};cache={}
def digest(b):return hashlib.sha256(b).hexdigest()
def tree(ref):
 if ref not in trees:
  d={}
  for entry in subprocess.check_output(['git','ls-tree','-r','-z',ref],cwd=REPO).split(b'\0'):
   if not entry:continue
   meta,path=entry.split(b'\t',1);mode,kind,obj=meta.decode().split();d[path.decode()]=(mode,kind,obj)
  trees[ref]=d
 return trees[ref]
def read(path,ref=None):
 global blob
 q=Path(path);assert not q.is_absolute() and '..' not in q.parts,path
 if ref:
  mode,kind,obj=tree(ref)[str(q)];assert mode in {'100644','100755'} and kind=='blob',(ref,path,mode)
  if obj not in cache:
   if blob is None:blob=subprocess.Popen(['git','cat-file','--batch'],cwd=REPO,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
   blob.stdin.write((obj+'\n').encode());blob.stdin.flush();h=blob.stdout.readline().decode().strip().split();assert h[0]==obj and h[1]=='blob',h
   data=blob.stdout.read(int(h[2]));assert blob.stdout.read(1)==b'\n';cache[obj]=data
  return cache[obj]
 f=REPO/q;assert f.is_file() and not f.is_symlink(),path;return f.read_bytes()
def close():
 if blob is not None:
  blob.stdin.close();blob.stdout.close();blob.wait()
atexit.register(close)
def js(path,ref=None):return json.loads(read(path,ref))
def bound(rec,ref=None):
 data=read(rec['path'],ref);assert digest(data)==rec['sha256'],rec['path'];return data
idx_path=str((B/'ACCEPTANCE_INDEX.json').relative_to(REPO));idx=js(idx_path,a.git_ref)
assert idx['modules']==20 and idx['number_of_independent_fresh_runs']==6
assert idx['sum_of_separate_run_commands']==109 and not idx['single_combined_109_command_run_performed']
assert idx['new_kernel_commands_for_this_index']==0 and idx['problem_status']=='Solved; unchanged'
for field in ['complete_RE05_Target_proved','actual_copy_success_probability_proved','OriginalClaim_or_SourceCompanion_proved','new_Linux_or_Comparator_acceptance']:assert not idx[field],field
for path,h in idx['artifact_sha256'].items():assert digest(read(path,a.git_ref))==h,path
for path,h in idx['TR04_canonical205_sha256'].items():assert digest(read(path,a.git_ref))==h,path
assert len(idx['TR04_canonical205_sha256'])==205 and len(js('problem_ids.json',a.git_ref))==217
input_lock=json.loads(bound(idx['original18_lock'],a.git_ref));assert len(input_lock['source_inputs'])==18
for x in input_lock['source_inputs']:assert digest(read(x['path'],a.git_ref))==x['sha256'],x['path']
allowed={'propext','Classical.choice','Quot.sound'};covered=set();commands=producers=positive=negative=0;scope_reports=[]
for scope in idx['independent_fresh_runs']:
 acceptance=json.loads(bound(scope['acceptance'],a.git_ref));c=json.loads(bound(scope['source_lock'],a.git_ref));r=json.loads(bound(scope['result'],a.git_ref))
 assert acceptance['passed'] and r['passed'] and 'exception' not in r
 assert not r['project_objects_reused'] and r['private_objects_removed']
 assert r['compiler_binary_sha256']=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
 assert '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in r['compiler']
 for key in ['pins_before','pins_after']:assert len(r[key])==10 and all(x['clean'] for x in r[key])
 assert r['pins_before']==r['pins_after']
 for key in ['original18_before','original18_after']:assert len(r[key])==18 and all(x['passed'] for x in r[key])
 assert r['original18_before']==r['original18_after'] and r['TR04_before']['passed'] and r['TR04_after']['passed']
 assert not r['full_RE05_Target_proved'] and not r['probability_99of100_proved'] and not r['OriginalClaim_or_SourceCompanion_proved'] and not r['Linux_or_Comparator_acceptance']
 assert len(r['commands'])==scope['actual_kernel_commands'] and len(c['union'])==scope['separately_fresh_project_producers']
 for rec in c['union']:assert digest(read(rec['path'],a.git_ref))==rec['sha256'],rec['path']
 logs={};runroot=str(Path(scope['result']['path']).parent)
 for cmd in r['commands']:
  assert cmd['exit_code']==cmd['expected_exit_code'];raw=read(str(Path(runroot)/cmd['log']),a.git_ref);assert digest(raw)==cmd['log_sha256'];logs[cmd['source']]=raw.decode()
 assert [(x['source'],x['exit_code']) for x in r['commands'] if x['exit_code']]==[('SorryControl.lean',1),('PrivateControl.lean',1),('TargetDefinitionControl.lean',1)]
 for block in c['blocks']:
  info=r['blocks'][block['key']];assert info['passed']
  log=logs[r['consumer_bindings'][block['key']]['source']]
  kinds=re.findall(r'AUDITED_KIND (\S+) (\S+)',log);actual=re.findall(r'AUDITED_ACTUAL (\S+) (\S+) (\S+)',log);axs=re.findall(r'AUDITED_AXIOMS (\S+) \[([^\]]*)\]',log)
  expected=[(d['audit_id'],'theorem' if d['kind'] in {'theorem','lemma'} else 'inductive' if d['kind'] in {'structure','inductive'} else 'definition') for d in block['declarations']]
  assert sorted(kinds)==sorted(expected)
  assert sorted(actual)==sorted((d['name'],d['audit_id'],d['visibility']) for d in block['declarations'])
  assert sorted(n for n,_ in axs)==sorted(n for n,_ in expected)
  assert all({v.strip() for v in s.split(',') if v.strip()}<=allowed for _,s in axs)
  assert 'error:' not in log and 'sorryAx' not in log
  bindings=r['consumer_bindings'][block['key']]['literal_examples'];assert [x['name'] for x in bindings]==block['literal_endpoints']
  assert info['complete_raw_theorem_types']==len(bindings)
  covered.update(n for n,_ in expected)
 if 'composed_deterministic_query_cap' in r:
  comp=r['composed_deterministic_query_cap'];assert comp['passed'] and not comp['hcharge_or_hsource_premise']
  log=logs['IndependentQueryComposition.lean'];assert 'error:' not in log and 'sorryAx' not in log
  names=['RE05IndependentComposition.actual_query_cap','RE05IndependentComposition.uniform_deterministic_constants','RE05IndependentComposition.reviewed_Target_identity']
  assert sorted(re.findall(r'AUDITED_KIND (\S+) (\S+)',log))==sorted((n,'theorem') for n in names)
 for filename,kind in [('SorryControl.lean','sorry'),('PrivateControl.lean','private_axiom'),('TargetDefinitionControl.lean','kind')]:
  log=logs[filename];assert log.count('error:')==1
  axs=re.findall(r'AUDITED_AXIOMS (\S+) \[([^\]]*)\]',log)
  if kind=='kind':assert 'constant kind differs from frozen source' in log and not axs
  else:
   assert 'depends on sorry or unrecognized axioms' in log and len(axs)==1
   expect={'sorryAx'} if kind=='sorry' else {'_private.PrivateControl.0.RE05Negative.hiddenFalse'}
   assert {x.strip() for x in axs[0][1].split(',') if x.strip()}==expect
   if kind=='private_axiom':assert axs[0][0]=='_private.PrivateControl.0.RE05Negative.privateProof'
  assert r['negative_controls'][kind]['passed'] and not r['negative_controls'][kind]['accepted_as_proof']
 commands+=len(r['commands']);producers+=len(c['union']);positive+=scope['positive_consumer_count'];negative+=3
 scope_reports.append({'directory':scope['directory'],'commands':len(r['commands']),'producer_commands':len(c['union']),'positive_consumers':scope['positive_consumer_count'],'expected_rejections':3,'passed':True})
assert (commands,producers,positive,negative)==(109,80,11,18)
census=json.loads(bound(idx['source_census'],a.git_ref));assert len(census['RE05_modules'])==20
assert (census['RE05_explicit_named_declarations'],census['RE05_definitions'],census['RE05_theorems'],census['RE05_public_names'],census['RE05_private_names'])==(156,24,132,152,4)
assert len(census['closure_source_records'])==28 and len(census['closure_declarations'])==267
assert {d['audit_id'] for d in census['closure_declarations']}==covered
assert len(census['all_closure_private_audit_ids'])==4 and all('GaussianMoments.0.' in n for n in census['all_closure_private_audit_ids'])
for fail in idx['retained_failures']:
 d=json.loads(bound(fail,a.git_ref));assert d['passed'] is False and len(d['commands'])==fail['actual_commands'] and not fail['accepted']
# Earlier aggregate manifests are checked at their own immutable commits, never relabelled against today's aggregate.
historical=[]
for rec in idx['historical_checkpoints']:
 d=json.loads(bound(rec,a.git_ref));ref=rec['immutable_git_ref'];assert digest(read(rec['path'],ref))==rec['sha256']
 for path,h in d['file_sha256'].items():assert digest(read(path,ref))==h,(ref,path)
 for path,h in d['TR04_canonical205_sha256'].items():assert digest(read(path,ref))==h,(ref,path)
 assert len(js('problem_ids.json',ref))==217
 historical.append({'checkpoint':rec['path'],'immutable_git_ref':ref,'historical_files_verified':len(d['file_sha256']),'TR04_verified':205,'passed':True})
wiring=json.loads(bound(idx['aggregate_wiring_review'],a.git_ref));assert wiring['passed'] and len(wiring['resolved_RE05_proof_modules'])==20
assert digest(read(wiring['file'],a.git_ref))==wiring['after_sha256']==idx['current_aggregate_sha256']
assert digest(read(wiring['file'],wiring['git_ref_before']))==wiring['before_sha256']
before=read(str(B.relative_to(REPO)/'before-Proofs.lean.txt'),a.git_ref);after=read(str(B.relative_to(REPO)/'after-Proofs.lean.txt'),a.git_ref)
assert after.replace(wiring['exact_added_utf8'].encode(),b'',1)==before
out={'passed':True,'index_sha256':digest(read(idx_path,a.git_ref)),'git_ref':a.git_ref,'bound_artifacts_verified':len(idx['artifact_sha256']),'scoped_run_reports':scope_reports,'sum_of_separate_command_counts':commands,'single_combined_kernel_run':False,'new_kernel_commands':0,'RE05_modules':20,'RE05_explicit_names':156,'audited_project_name_union':267,'private_helpers':4,'original_inputs_verified':18,'permanent_IDs':217,'TR04_canonical_inputs_verified':205,'historical_checkpoints':historical,'complete_RE05_Target_proved':False,'event_success_probability_proved':False,'new_CI_or_Comparator_acceptance':False}
if a.report:
 assert not a.report.exists();a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
