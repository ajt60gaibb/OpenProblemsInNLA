"""Summarize only actual independently produced RA09 referee2 evidence.
No theorem is accepted from a textual scan or from someone else's verdict.
"""
from pathlib import Path
import hashlib,json,re,subprocess,datetime
E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
past=json.loads((E/'fresh-result.json').read_text());resume=json.loads((E/'resume-result.json').read_text())
assert past['verdict']=='FAIL' and resume['verdict']=='PASS'
assert resume['prior_result_sha256']==sha(E/'fresh-result.json')
assert resume['disposable_prefix_removed_after_check'] and not Path(resume['prefix']).exists()
commands=past['commands']+resume['commands']
success=[x for x in commands if x['exit_code']==0];fail=[x for x in commands if x['exit_code']!=0]
assert len(commands)==20 and len(success)==19 and len(fail)==1
for row in commands:
 assert sha(E/row['log'])==row['log_sha256'] and sha(E/row['source_snapshot'])==row['source_sha256']
assert 'invalid \'import\' command, it must be used in the beginning of the file' in (E/fail[0]['log']).read_text()
assert sha(E/'Inspect.lean')==resume['commands'][0]['source_sha256']
reference=(P/'Challenge.lean').read_text().replace('namespace NLA.RA09','namespace NLA.RA09.FinalReferee2Reference').replace('end NLA.RA09','end NLA.RA09.FinalReferee2Reference')
assert (E/'Reference.lean').read_text()==reference
trust=[];warning_count=0
for row in success:
 text=(E/row['log']).read_text();source=(E/row['source_snapshot']).read_text()
 assert 'error:' not in text
 if row['source'].endswith('/Reference.lean'):
  assert text.count('warning: declaration uses `sorry`')==17 and text.count('warning:')==17
  warning_count+=17
 else:
  assert 'warning:' not in text
  for decl,axs in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S):
   names=[x.strip() for x in axs.split(',') if x.strip()]
   assert set(names)<={'propext','Classical.choice','Quot.sound'}
   trust.append({'declaration':decl,'axioms':names,'log':row['log']})
  assert len(re.findall(r'^#assert_trust kernel ',source,re.M))==len(re.findall('depends on axioms:',text))
assert len(trust)==50
(E/'axioms.json').write_text(json.dumps({'verdict':'PASS','explicit_LeanCert_kernel_assertions':50,
 'actual_printed_standard_three_reports':trust,'reference_warning_count':warning_count,
 'LeanCert_scope':'#assert_trust kernel actual theorem-axiom classification executed in 16 fresh implementation sources and the literal consumer. No interval certificate is asserted or needed for this pure exact proof.'},indent=2)+'\n')
t=(E/'Inspect-retry.log').read_text()
names=json.loads((P/'comparator.json').read_text())['theorem_names']
assert re.findall(r'REFEREE2_EXACT_TYPE (NLA\.RA09\.\w+):',t)==names
edges={label:[] for label in ['FINAL_TARGET','ALL_EXPORTS']}
for label,name,ds in re.findall(r'^PROJECT_EDGE (\w+) ([^:]+): \[(.*?)\]',t,re.M|re.S):
 deps=[x.strip() for x in ds.split(',') if x.strip()]
 assert not any('Reference' in x for x in [name,*deps])
 edges[label].append({'declaration':name,'direct_project_type_or_body_dependencies':deps})
actualaxs={label:[] for label in edges}
for label,name,axs in re.findall(r'^ACTUAL_AXIOMS (\w+) ([^:]+): \[(.*?)\]',t,re.M|re.S):
 an=[x.strip() for x in axs.split(',') if x.strip()]
 assert set(an)<={'propext','Classical.choice','Quot.sound'}
 actualaxs[label].append({'declaration':name,'axioms':an})
required={label:re.findall(r'^RETAINED_DEPENDENCY '+label+r': ([^\n]+)',t,re.M) for label in edges}
for label,n,m in [('FINAL_TARGET',115,40),('ALL_EXPORTS',139,49)]:
 assert len(edges[label])==len(actualaxs[label])==n and len(required[label])==m
 assert len({r['declaration'] for r in edges[label]})==n
 assert f'PROJECT_COUNTS {label}: declarations={n}, required={m}' in t
assert '@Matrix.frobeniusNormedAddCommGroup' in t
assert '@cfc.' in t and 'def NLA.RA09.ConcaveFrobeniusTransferConjecture' in t
(E/'actual-proof-dependencies.json').write_text(json.dumps({'verdict':'PASS','inspector_sha256':sha(E/'Inspect.lean'),
 'raw_fresh_log':'Inspect-retry.log','raw_fresh_log_sha256':sha(E/'Inspect-retry.log'),
 'exact_elaborated_types':names,'traversal':'Actual declaration types and available opaque proof bodies; reject unsafe, partial, bodyless non-structural declarations and all nonstandard transitive axioms; terminate only after worklist empty.',
 'project_edges':edges,'project_transitive_axioms':actualaxs,'required_material_dependencies':required,
 'statement_reference':'Exact namespace-only derived Challenge; only used for type elaboration. Each has deliberate sorryAx, none is in actual theorem closure.',
 'scope':'Local Lean elaboration and actual project dependency audit, not authoritative Linux Comparator.'},indent=2)+'\n')
f=json.loads((P/'verification/proof-freeze.json').read_text())
for name,h in f['files'].items():assert sha(P/name)==h,name
for name,h in f['source_files'].items():
 raw=subprocess.check_output(['git','show',f['base']+':'+name],cwd=W)
 assert hashlib.sha256(raw).hexdigest()==h and (W/name).read_bytes()==raw
assert sha(P/'reviews/proof-completion.md')=='b8518dfa6201370f1f8ecefc58f0260c9a889acbbc256db774fc046192197297'
result={'verdict':'APPROVE','reviewer':'/root/mf16_final_referee','role':'Independent final mathematical referee 2, no RA09 statement or implementation contribution',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'proof_freeze_sha256':sha(P/'verification/proof-freeze.json'),
 'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),'proof_completion_sha256':sha(P/'reviews/proof-completion.md'),
 'successful_direct_Lean_commands':19,'failed_Lean_commands':1,'failed_scope':'Reviewer-only import ordering, raw diagnostic retained; no mathematical proof error.',
 'complete_original_target':True,'actual_frobenius_norm_CFC_consumer':'RA09FinalReferee2.original_norm_target',
 'exact_export_count':17,'explicit_kernel_trust_and_standard_three_reports':50,
 'actual_project_closure_counts':{'final_target':115,'all_exports':139},'required_material_dependency_counts':{'final_target':40,'all_exports':49},
 'source_boundary':{'proof_inputs':361,'original_sources':17,'nested_prior_manifests':7,'all_unchanged':True},
 'own_disposable_objects_removed_after_hashing':len(resume['objects_hashed_before_cleanup']),
 'own_disposable_bytes_removed':sum(x['bytes'] for x in resume['objects_hashed_before_cleanup']),
 'no_Lake_or_dependency_download_copy_rebuild':True,'no_implementation_or_canonical_edit':True,
 'actual_Linux_Comparator_sandbox_standalone_kernel_replay':'Not run or accepted by this local mathematical review; later separate gate.',
 'nonblocking_finding':'OrderedExistence.lean:8 attribution says counterexample for the affirmative theorem. Frozen bytes preserved.',
 'evidence':{x:sha(E/x) for x in ['fresh-result.json','resume-result.json','axioms.json','actual-proof-dependencies.json','source-audit.json','primary-and-review-inputs.json','inspector-import-correction.json']}}
(E/'final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['verdict','successful_direct_Lean_commands','failed_Lean_commands','exact_export_count','explicit_kernel_trust_and_standard_three_reports','actual_project_closure_counts']}))
