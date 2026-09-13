"""Seal complete RA09 proof after actual fresh checks, retaining all raw evidence.
Exact self exclusion; every nested manifest remains an ordinary bound input.
The subsequent completion report and independent referee files are additive.
"""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
P=Path(__file__).resolve().parents[2];W=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
freeze=P/'verification/proof-freeze.json'
assert not freeze.exists()
sf=json.loads((P/'reviews/statement-freeze.json').read_text())
for name,h in sf['files'].items():assert sha(P/name)==h,name
for name,h in sf['source_files'].items():
    raw=subprocess.check_output(['git','show',sf['base']+':'+name],cwd=W)
    assert hashlib.sha256(raw).hexdigest()==h and (W/name).read_bytes()==raw,name
latest=json.loads((P/'verification/final/latest.json').read_text())
attempt=Path(latest['attempt']);result=attempt/'result.json';r=json.loads(result.read_text())
assert sha(result)==latest['result_sha256'] and r['verdict']=='PASS'
assert len(r['commands'])==18 and len(r['pins'])==10
logtext=''
for c in r['commands']:
    assert c['exit_code']==0 and sha(P/c['source'])==c['source_sha256']
    log=attempt/c['log'];assert sha(log)==c['log_sha256'];logtext+=log.read_text()+'\n'
    if c["source"]=="Challenge.lean": assert log.read_text().count("warning: declaration uses `sorry`")==17
    else: assert "warning:" not in log.read_text() and "error:" not in log.read_text()
assert len(re.findall('depends on axioms:',logtext))==49
for closure in re.findall(r'depends on axioms: \[(.*?)\]',logtext):
    assert set(x.strip() for x in closure.split(','))<={'propext','Classical.choice','Quot.sound'}
assert 'PROJECT_COUNTS FINAL_TARGET: declarations=115, required=31' in logtext
assert 'PROJECT_COUNTS ALL_EXPORTS: declarations=139, required=39' in logtext
audit=json.loads((P/'verification/final/source-audit.json').read_text())
for name,h in audit['mathematical_inputs'].items():assert sha(P/name)==h,name
exclude={freeze,P/'reviews/proof-completion.md'}
files={}
for path in sorted(P.rglob('*')):
    if not path.is_file() or path in exclude:continue
    rel=str(path.relative_to(P))
    assert not any(s in path.parts for s in ['.lake','__pycache__']),rel
    assert path.suffix not in ['.olean','.ilean'],rel
    files[rel]=sha(path)
record={
 'phase':'COMPLETE implementation before two independent final mathematical reviews and actual Linux',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base':sf['base'],
 'source_files':sf['source_files'],'source_git_blobs':sf['source_git_blobs'],
 'source_file_count':len(sf['source_files']),'files':files,'file_count':len(files),
 'statement_freeze_sha256':sha(P/'reviews/statement-freeze.json'),
 'all_statement_inputs_unchanged':len(sf['files']),
 'accepted_statement_gate_sha256':sha(P/'verification/proof-start.json'),
 'mathematical_inputs':audit['mathematical_inputs'],
 'successful_fresh_source_commands':18,'source_kernel_standard_three_reports':49,
 'actual_final_target_traversal':{'project_declarations':115,'required_dependencies':31},
 'actual_all_exports_traversal':{'project_declarations':139,'required_dependencies':39},
 'fresh_result':str(result.relative_to(P)),'fresh_result_sha256':sha(result),
 'fresh_inspector_sha256':sha(P/'verification/final/Inspect.lean'),
 'source_audit_sha256':sha(P/'verification/final/source-audit.json'),
 'exports':audit['exact_reference_export_signatures'],'definition_exceptions':[],
 'axioms':['propext','Classical.choice','Quot.sound'],
 'LeanCert_scope':'Actual explicit kernel trust audits and transitive project/type/body/axiom inspection of pure exact proofs; no interval certificate or native execution.',
 'complete_scope':'All original quantifiers and actual Frobenius/CFC/order/truncation semantics, canonical difference-of-squares premise, f(0)>0, f(tau)=0, positive and zero tails, every eigenbasis; full affirmative target.',
 'raw_evidence':'All successful and failed author/helper/statement diagnostic sources and logs retained, including the audit-only corrected nonexistent primary API path and root temporary ENOSPC before a command ran.',
 'inventory_rule':'Every actual project file including nested EVIDENCE-MANIFEST.json files; excludes only this exact proof-freeze.json and the subsequent reviews/proof-completion.md. Independent reviews and later candidate metadata are additive, with exact archival exceptions required for historical wrappers.',
 'nested_evidence_manifests_bound':[n for n in files if Path(n).name=='EVIDENCE-MANIFEST.json'],
 'contributors_ineligible_as_independent_final_referees':['/root/leancert_examples','/root','/root/formal_review_standards','/root/solved_statement_inventory'],
 'canonical_status':'Solved, unchanged','Linux_Comparator_default_kernel_controls':'pending',
 'no_commit_push_or_status_change':True}
freeze.write_text(json.dumps(record,indent=2)+'\n')
for name,h in files.items():assert sha(P/name)==h,name
print('SEALED',len(files),'+',len(sf['source_files']),'proof freeze',sha(freeze))
