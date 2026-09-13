"""Seal the complete RA08 proof and retained evidence for independent final review."""
from pathlib import Path
import datetime, hashlib, json, re
P=Path(__file__).resolve().parents[2]
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
statement=json.loads((P/'reviews/statement-freeze.json').read_text())
for name,h in statement['files'].items(): assert sha(P/name)==h,name
latest=json.loads((E/'latest.json').read_text());run=Path(latest['attempt'])
assert sha(run/'result.json')==latest['result_sha256']
result=json.loads((run/'result.json').read_text())
assert result['verdict']=='PASS' and len(result['commands'])==19
assert result['pins_rechecked_after'] and result['disposable_prefix_removed_after_check']
closures=[]
for row in result['commands']:
    assert row['exit_code']==0 and sha(P/row['source'])==row['source_sha256'],row['source']
    assert sha(run/row['log'])==row['log_sha256']
    text=(run/row['log']).read_text()
    if row['source']=='Challenge.lean':
        assert text.count('warning: declaration uses `sorry`')==14 and text.count('warning:')==14
    else: assert 'warning:' not in text and 'error:' not in text
    closures.extend(re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text))
assert len(closures)==59
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(x.strip() for x in c.split(','))==allowed for _,c in closures)
inspect=run/'verification-final-Inspect.log';text=inspect.read_text()
retained=re.findall(r'RETAINED_DEPENDENCY: ([^\n]+)',text)
count=int(re.search(r'PROJECT_DECLARATIONS_REACHABLE_FROM_FULL_NEGATION: (\d+)',text).group(1))
assert len(retained)==33 and count==215
assert 'NUMERICAL_HELPER NLA.RA08.numerical_gap_positive_proved._proof_1_7:' in text
assert 'LeanCert.Validity.verify_strict_upper_bound_dyadic_checked' in text
assert 'NLA.RA08.numerical_gap_positive_proved' in text.split('PROJECT_EDGE NLA.RA08.counterexample_proved:',1)[1].split('PROJECT_EDGE',1)[0]
(E/'axiom-reports.json').write_text(json.dumps({'reports':[{'name':n,'axioms':c.split(', ')} for n,c in closures],'count':len(closures),'allowed':sorted(allowed)},indent=2)+'\n')
(E/'actual-dependencies.json').write_text(json.dumps({'inspector_sha256':sha(inspect),'full_negation_project_declarations':count,'required_retained_dependencies':retained,'material_certificate_helper':'NLA.RA08.numerical_gap_positive_proved._proof_1_7','actual_certificate_expression':'constant 0 on singleton [0,0]','strict_upper_bound':'78605142319958855341529309 / 11432529876841442781954048000'},indent=2)+'\n')
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'phase':'Complete local proof frozen for two independent final mathematical reviews',
 'implementation_agents':['/root/formal_review_standards','/root','/root/solved_statement_inventory'],
 'required_independent_final_referees':['/root/leancert_examples','new agent without RA08 authorship'],
 'reviewed_exports':json.loads((P/'comparator.json').read_text())['theorem_names'],
 'statement_inputs_preserved':len(statement['files']),'original_source_Git_blobs_preserved':len(statement['source_files']),
 'exact_reference_export_signatures':True,'definition_exceptions':[],
 'fresh_result':str((run/'result.json').relative_to(P)),'fresh_result_sha256':sha(run/'result.json'),
 'fresh_commands':len(result['commands']),'kernel_standard_three_reports':len(closures),
 'implementation_warnings':0,'separate_reference_placeholders':14,
 'project_declarations_from_full_negation':count,'required_retained_dependencies':len(retained),
 'actual_inspection_sha256':sha(inspect),'source_audit_sha256':sha(E/'source-audit.json'),
 'exact_clean_readonly_pins':len(result['pins']),
 'statement_gate_sha256':sha(P/'verification/proof-start.json'),
 'implementation_roles_sha256':sha(P/'verification/implementation-roles.json'),
 'proof_map_sha256':sha(P/'PROOF_MAP.md'),'completion_report_sha256':sha(P/'reviews/proof-completion.md'),
 'LeanCert_scope':'Material explicit-kernel singleton positive rational gap; no interval subdivisions or native execution trust.',
 'original_stronger_contour_ratio':'Not claimed; weaker exact polynomial strict gap gives complete target negation.',
 'local_platform':result['platform'],'scope_limit':'Local macOS source elaboration; no Linux Comparator result or independent final approval.',
 'canonical_status':'Solved, unchanged','Linux_Comparator':'pending','publication':'pending'}
(E/'completion-checks.json').write_text(json.dumps(record,indent=2)+'\n')
outer=P/'verification/proof-freeze.json'
files={}
for path in sorted(P.rglob('*')):
    rel=path.relative_to(P)
    if not path.is_file() or path==outer: continue
    if any(x in rel.parts for x in ['.git','.lake','__pycache__']): continue
    if path.suffix in ['.olean','.ilean','.trace','.pyc']: continue
    files[str(rel)]=sha(path)
freeze={'phase':record['phase'],'utc':record['utc'],'base':statement['base'],'branch':statement['branch'],
 'file_count':len(files),'files':files,'source_file_count':len(statement['source_files']),
 'source_files':statement['source_files'],'source_git_blobs':statement['source_git_blobs'],
 'preserved_statement_inputs':len(statement['files']),'complete_local_checks':record,
 'outer_exact_self_exclusion':'verification/proof-freeze.json','nested_manifests_preserved':True,
 'generated_object_exclusions':['.lake','.git','__pycache__','.olean','.ilean','.trace','.pyc']}
outer.write_text(json.dumps(freeze,indent=2)+'\n')
print('FROZEN',len(files),'project +',len(statement['source_files']),'source Git blobs')
for name in ['NLA/RA08/Proof.lean','Solution.lean','PROOF_MAP.md','reviews/proof-completion.md','verification/proof-freeze.json']:
 print(name,sha(P/name))
