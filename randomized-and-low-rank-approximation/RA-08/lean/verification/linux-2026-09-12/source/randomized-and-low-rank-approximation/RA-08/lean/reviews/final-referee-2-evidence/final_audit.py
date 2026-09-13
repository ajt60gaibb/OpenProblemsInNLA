"""Final independent integrity audit, with exact original freeze and raw evidence checks."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;P=E.parents[1];R=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda n,x:(E/n).write_text(json.dumps(x,indent=2)+'\n')
fz='ab05e2bf801e6906453e88a4d84d5e73191f776db05610fb8b8e5e4a03d4f856'
assert sha(P/'verification/proof-freeze.json')==fz
F=json.loads((P/'verification/proof-freeze.json').read_text())
assert len(F['files'])==450 and len(F['source_files'])==10
for rel,h in F['files'].items():
 p=P/rel;assert p.is_file() and not p.is_symlink() and sha(p)==h,rel
S=json.loads((P/'reviews/statement-freeze.json').read_text())
assert len(S['files'])==39
assert sha(P/'reviews/statement-freeze.json')=='eb0460c3dd4c13a42f928e3f00c9c3710e486922b99aff74f4d6a3098c5ed332'
for rel,h in S['files'].items():assert sha(P/rel)==h,rel
for rel,h in F['source_files'].items():
 raw=subprocess.check_output(['git','-C',str(R),'show',F['base']+':'+rel])
 assert (R/rel).read_bytes()==raw and hashlib.sha256(raw).hexdigest()==h,rel
 assert subprocess.check_output(['git','-C',str(R),'rev-parse',F['base']+':'+rel]).decode().strip()==F['source_git_blobs'][rel]
assert sha(P/'reviews/proof-completion.md')=='dab07a0cf99d739914c54efea282211afcbfb45507ac3fef74b285afc3ad79ce'
assert sha(P/'verification/proof-start.json')=='5574e03e0344d9afef4a6e6baa11563789312456b4d14c1f853eb79d14ebca4f'
nested=[]
for rel in F['files']:
 if Path(rel).name!='EVIDENCE-MANIFEST.json':continue
 p=P/rel;m=json.loads(p.read_text());expected=set()
 for name,r in m['files'].items():
  target=p.parent/name;h=r['sha256'] if isinstance(r,dict) else r
  assert sha(target)==h,(rel,name)
  if isinstance(r,dict) and 'bytes' in r:assert target.stat().st_size==r['bytes']
  if not name.startswith('../'):expected.add(name)
 actual={str(f.relative_to(p.parent)) for f in p.parent.rglob('*') if f.is_file() and f!=p}
 assert actual==expected,(rel,actual-expected,expected-actual)
 if 'file_count' in m:assert m['file_count']==len(m['files'])
 nested.append({'path':rel,'sha256':sha(p),'bound_files':len(m['files']),'complete_inventory':True})
assert len(nested)==4
record=json.loads((E/'fresh-checks.json').read_text())
assert record['successful_commands']==19 and record['failed_reviewer_diagnostic_commands']==1
assert len(record['commands'])==20 and sum(c['exit_code']==0 for c in record['commands'])==19
for i,c in enumerate(record['commands']):
 assert sha(E/c['log'])==c['log_sha256']
 source=P/c['source']
 if c['exit_code']==1:source=E/'initial-diagnostic-clm-parameters/Inspect.lean.txt'
 assert sha(source)==c['source_sha256'],c['source']
 if i<18:
  snapshot=E/(c['source'].removesuffix('.lean').replace('/','-')+'.lean.txt')
  assert sha(snapshot)==c['source_sha256']
 raw=(E/c['log']).read_bytes()
 if c['exit_code']==0:
  holes=14 if c['source']=='Challenge.lean' else 0
  assert raw.count(b'warning:')==holes
  assert raw.count(b'declaration uses '+bytes([96])+b'sorry'+bytes([96]))==holes
  assert b'error:' not in raw
 else:
  assert raw.count(b'error: Function expected at')==4
A=json.loads((E/'axioms.json').read_text())
assert A['count']==len(A['reports'])==62
for r in A['reports']:assert r['axioms']==['propext','Classical.choice','Quot.sound']
for f in ['actual-proof-dependencies.json','exact-reconstruction.json','primary-and-review-inputs.json','permanent-target-check.json']:
 assert json.loads((E/f).read_text())['result']=='PASS',f
D=json.loads((E/'actual-proof-dependencies.json').read_text())
assert D['counts']==[['FINAL_TARGET','215','3'],['ALL_EXPORTS','237','3']]
assert len(D['required_consumed'])==82 and D['final_target_separately_traversed']
text=(E/'Inspect-retry.log').read_text()
assert 'NLA.RA08.numerical_gap_positive_proved._proof_1_7' in text
assert 'LeanCert.Validity.verify_strict_upper_bound_dyadic_checked' in text
assert '@of_decide_eq_true' in text and '(@Eq.refl.{1} Bool Bool.true)' in text
assert 'Lean.ofReduceBool' not in text and 'Lean.trustCompiler' not in text
cleanup=json.loads((E/'disposable-object-cleanup.json').read_text())
assert cleanup['file_count']==36 and cleanup['phase']=='completed'
objects={rel:h for c in record['commands'][:18] for rel,h in c['fresh_objects'].items()}
assert set(cleanup['removed_files'])==set(objects)
for rel,r in cleanup['removed_files'].items():assert r['sha256']==objects[rel]
assert not Path(record['fresh_prefix']).exists()
assert json.loads((E/'integrity-before.json').read_text())==json.loads((E/'integrity-after.json').read_text())
pins=json.loads((E/'dependency-pins-before.json').read_text())
assert pins==json.loads((E/'dependency-pins-after.json').read_text())
for p in pins:
 assert subprocess.check_output(['git','-C',p['path'],'rev-parse','HEAD']).decode().strip()==p['revision']
 assert not subprocess.check_output(['git','-C',p['path'],'status','--porcelain=v1'])
def headers(p):
 s=p.read_text();return {m.group(1):' '.join(s[m.end():s.index(':=',m.end())].split())
  for m in re.finditer(r'^theorem\s+(\w+)\s+',s,re.M)}
assert headers(P/'Challenge.lean')==headers(P/'Solution.lean')
assert len(headers(P/'Solution.lean'))==14
cfg=json.loads((P/'comparator.json').read_text())
assert cfg['theorem_names']==['NLA.RA08.'+n for n in headers(P/'Solution.lean')]
assert cfg['definition_names']==[] and cfg['permitted_axioms']==['propext','Classical.choice','Quot.sound']
report=E.parent/'final-referee-2.md'
assert report.is_file() and 'No unresolved mathematical finding.' in report.read_text()
save('final-audit.json',{'result':'PASS','proof_freeze_sha256':fz,'project_inputs_preserved':450,
 'original_source_files_preserved':10,'statement_inputs_preserved':39,'nested_manifests':nested,
 'fresh_successful_source_commands':19,'preserved_reviewer_diagnostic_failure':1,
 'standard_three_axiom_reports':62,'actual_dependency_traversals':D['counts'],
 'required_dependencies_per_traversal':41,'complete_original_target_review':'APPROVE',
 'canonical_status':'Solved, unchanged','Linux_Comparator_and_default_kernel_run':False,
 'new_metadata_schema_validation':False,'publication_review':False,
 'reviewer':'/root/mf16_final_referee','independent_final_referee_number':2,
 'report_sha256':sha(report)})
print(json.dumps({'result':'PASS','project_files':450,'originals':10,'statement_files':39,
 'nested_manifests':len(nested),'report_sha256':sha(report)}))
