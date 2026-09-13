"""Final independent integrity audit; does not recompile or change the candidate."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;P=E.parents[1];R=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda n,x:(E/n).write_text(json.dumps(x,indent=2)+'\n')
fz='f4b21be066d0e55e56aae5b3fd1119433ef09d7ed5822d57dacab906b38ac720'
assert sha(P/'verification/proof-freeze.json')==fz
F=json.loads((P/'verification/proof-freeze.json').read_text())
assert len(F['files'])==182 and len(F['source_files'])==14
for rel,h in F['files'].items():
 p=P/rel;assert p.is_file() and not p.is_symlink() and sha(p)==h,rel
S=json.loads((P/'reviews/statement-freeze.json').read_text())
assert len(S['files'])==45
for rel,h in S['files'].items():assert sha(P/rel)==h
for rel,h in F['source_files'].items():
 raw=subprocess.check_output(['git','-C',str(R),'show',F['base']+':'+rel])
 assert (R/rel).read_bytes()==raw and hashlib.sha256(raw).hexdigest()==h
assert sha(P/'reviews/proof-completion.md')=='ad86420d1e3640da6c2edacfc4160a259a766a59764f1f764ca4caa7e1082f78'
assert sha(P/'verification/proof-start.json')=='9070bf321c98230b8ada5ede4501710be5d2597dc820c8023c45900d8aef623b'
nested=[]
for rel in F['files']:
 if Path(rel).name!='EVIDENCE-MANIFEST.json':continue
 p=P/rel;m=json.loads(p.read_text())
 expected=set()
 for name,record in m['files'].items():
  target=p.parent/name
  h=record['sha256'] if isinstance(record,dict) else record
  assert sha(target)==h,(rel,name)
  if isinstance(record,dict) and 'bytes' in record:assert target.stat().st_size==record['bytes']
  if not name.startswith('../'):expected.add(name)
 actual={str(f.relative_to(p.parent)) for f in p.parent.rglob('*') if f.is_file() and f!=p}
 assert actual==expected,(rel,actual-expected,expected-actual)
 if 'file_count' in m:assert m['file_count']==len(m['files'])
 nested.append({'path':rel,'sha256':sha(p),'bound_files':len(m['files']),'complete_internal_inventory':True})
record=json.loads((E/'fresh-checks.json').read_text())
assert record['successful_commands']==10 and record['failed_reviewer_diagnostic_commands']==1
assert len(record['commands'])==11 and sum(c['exit_code']==0 for c in record['commands'])==10
for c in record['commands']:
 assert sha(E/c['log'])==c['log_sha256']
 source=P/c['source']
 if c['exit_code']==1:source=E/'initial-diagnostic-namespace/Inspect.lean'
 assert sha(source)==c['source_sha256']
 raw=(E/c['log']).read_bytes()
 if c['exit_code']==0:
  holes=9 if c['source']=='Challenge.lean' else 0
  assert raw.count(b'warning:')==holes
  assert raw.count(b'declaration uses '+bytes([96])+b'sorry'+bytes([96]))==holes
  assert b'error:' not in raw
 else:
  assert b'Unknown identifier '+bytes([96])+b'toJson'+bytes([96]) in raw
A=json.loads((E/'axioms.json').read_text())
assert A['count']==len(A['reports'])==26
for r in A['reports']:assert r['axioms']==['propext','Classical.choice','Quot.sound']
for f in ['actual-proof-dependencies.json','reconstruction.json','primary-and-review-inputs.json','permanent-target-check.json']:
 assert json.loads((E/f).read_text())['result']=='PASS'
D=json.loads((E/'actual-proof-dependencies.json').read_text())
assert D['counts']==[['FINAL_TARGET','94','8'],['ALL_EXPORTS','110','8']]
assert len(D['required_consumed'])==60 and D['final_target_separately_traversed']
assert 'NLA.MF16.actual_krawczyk_checked._proof_1_1' in (E/'Inspect-retry.log').read_text()
Q=json.loads((E/'reconstruction.json').read_text())
assert sha(E/'actual-numeric.json')==Q['input_sha256'] and sha(E/'reconstruct.py')==Q['script_sha256']
cleanup=json.loads((E/'disposable-object-cleanup.json').read_text())
assert cleanup['file_count']==18
objects={rel:h for c in record['commands'][:9] for rel,h in c['fresh_objects'].items()}
assert set(cleanup['removed_files'])==set(objects)
for rel,r in cleanup['removed_files'].items():assert r['sha256']==objects[rel]
before=json.loads((E/'integrity-before.json').read_text())
after=json.loads((E/'integrity-after.json').read_text())
assert before==after
assert json.loads((E/'dependency-pins-before.json').read_text())==json.loads((E/'dependency-pins-after.json').read_text())
report=E.parent/'final-referee-1.md'
assert report.is_file() and 'No unresolved mathematical finding.' in report.read_text()
save('final-audit.json',{'result':'PASS','proof_freeze_sha256':fz,
'full_frozen_project_inputs':182,'original_source_files':14,'original_statement_inputs':45,
'nested_manifests':nested,'fresh_successful_source_commands':10,
'preserved_reviewer_diagnostic_failure':1,'standard_three_axiom_reports':26,
'separate_final_target_and_all_export_dependency_traversals':D['counts'],
'complete_correspondence_review':'APPROVE; no mathematical corrections requested',
'canonical_status':'Solved, unchanged','Linux_Comparator_and_default_kernel_run':False,
'new_metadata_schema_validation':False,'publication_review':False,
'independent_referee':'/root/mf16_final_referee','report_sha256':sha(report)})
print(json.dumps({'result':'PASS','182_project_and_14_original_inputs_preserved':True,
'45_statement_inputs_preserved':True,'nested_manifests':len(nested),
'report_sha256':sha(report)}))
