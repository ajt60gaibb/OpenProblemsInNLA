"""Seal complete IS03 proof evidence without changing the statement boundary."""
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
assert len(result['commands'])==10 and result['pins_rechecked_after']
closures=[]
for row in result['commands']:
    assert row['exit_code']==0 and sha(P/row['source'])==row['sha256']
    assert sha(run/row['log'])==row['log_sha256']
    text=(run/row['log']).read_text()
    if row['source']=='Challenge.lean':
        assert text.count('warning: declaration uses `sorry`')==7
    else: assert 'warning:' not in text and 'error:' not in text
    closures.extend(re.findall(r'depends on axioms: \[(.*?)\]',text))
assert len(closures)==18
assert all(set(x.strip() for x in c.split(','))=={'propext','Classical.choice','Quot.sound'} for c in closures)
inspect=run/'verification-final-Inspect.log';text=inspect.read_text()
assert text.count('RETAINED_DEPENDENCY:')==32
assert 'PROJECT_DECLARATIONS_REACHABLE_FROM_FULL_NEGATION: 55' in text
assert 'LeanCert.Validity.verify_strict_upper_bound_dyadic_checked' in text
assert 'NLA.IS03.numerical_negative_moment._proof_1_7' in text
assert sha(P/'NLA/IS03/Newton.lean')=='451953080999a9b7aec73af27af178018fec6d340439c3b4081716165a7f1ddd'
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'phase':'Complete local proof frozen for two independent final reviews',
    'implementation_agents':['/root/solved_statement_inventory','/root (Newton helper)'],
    'independent_final_reviewers':['/root/leancert_examples','/root/formal_review_standards'],
    'seven_reviewed_exports_complete':True,'exact_reference_signatures':True,
    'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),
    'proof_gate_sha256':sha(P/'verification/proof-start.json'),
    'fresh_result':str((run/'result.json').relative_to(P)),
    'fresh_result_sha256':sha(run/'result.json'),
    'inspection_sha256':sha(inspect),'source_audit_sha256':sha(E/'source-audit.json'),
    'exact_diagnostic_sha256':sha(E/'exact-checks.json'),
    'fresh_source_checks':10,'kernel_axiom_reports':18,'allowed_axioms':['propext','Classical.choice','Quot.sound'],
    'actual_project_dependencies':55,'required_semantic_dependencies':32,
    'LeanCert_input':'(-8593 / 823543 : ℝ) < 0',
    'LeanCert_scope':'Explicit kernel singleton certificate actually retained in negative_moment, counterexample and full negation. No interval search.',
    'local_cache_scope':'Ten pinned clean MI22 dependency artifacts reused read-only. Fresh separate project prefix excludes every prior IS03 object. No download, dependency copy/rebuild or Lake build.',
    'canonical_status':'Solved, unchanged','independent_final_review':'pending','Linux_Comparator':'pending'}
(E/'completion-checks.json').write_text(json.dumps(record,indent=2)+'\n')
excluded={'verification/proof-freeze.json'}
files={}
for path in sorted(P.rglob('*')):
    rel=path.relative_to(P)
    if not path.is_file() or any(x in rel.parts for x in ['.git','.lake','__pycache__']): continue
    if path.suffix in ['.olean','.ilean','.trace','.pyc'] or str(rel) in excluded: continue
    files[str(rel)]=sha(path)
freeze={'phase':record['phase'],'utc':record['utc'],'base':statement['base'],
    'branch':'codex/lean-is03-derivative-realizability','file_count':len(files),'files':files,
    'source_file_count':len(statement['source_files']),'source_files':statement['source_files'],
    'preserved_statement_inputs':len(statement['files']),
    'implementation_agents':record['implementation_agents'],
    'independent_final_reviewers':record['independent_final_reviewers'],
    'complete_local_checks':record,'excluded_generated_objects':True,
    'self_exclusion_only_for_record':'verification/proof-freeze.json'}
(P/'verification/proof-freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
print('FROZEN',len(files),'+',len(statement['source_files']))
for name in ['NLA/IS03/Algebra.lean','NLA/IS03/Witness.lean','NLA/IS03/Spectral.lean',
             'NLA/IS03/Newton.lean','NLA/IS03/Numerical.lean','NLA/IS03/Proof.lean',
             'Solution.lean','reviews/proof-completion.md','verification/proof-freeze.json']:
    print(name,sha(P/name))
