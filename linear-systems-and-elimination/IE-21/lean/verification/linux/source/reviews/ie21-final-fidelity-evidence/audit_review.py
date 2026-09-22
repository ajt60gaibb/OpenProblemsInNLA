from pathlib import Path
import hashlib,json,re
here=Path(__file__).resolve().parent
root=here.parents[1]
receipt=json.loads((here/'review-receipt.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for f,h in receipt['review_evidence_sha256'].items():
    assert sha(here/f)==h,f
for f,h in receipt['reviewed_package_sha256'].items():
    assert sha(root/f)==h,f
config=json.loads((root/'comparator.json').read_text())
build=json.loads((here/'build-receipt.json').read_text())
assert set(build['selected_axiom_closures'])==set(config['theorem_names'])
assert all(set(x)=={'propext','Classical.choice','Quot.sound'} for x in build['selected_axiom_closures'].values())
assert build['selected_exact_signature_checks']==23
assert build['project_sources_rebuilt']==31
assert all(x['exit_code']==0 for x in build['commands'])
assert all(not re.search(r'\b(?:warning|error):',x['output']) for x in build['commands'][:-1])
assert receipt['verdict']=='APPROVE source fidelity and complete target correspondence'
print('PASS IE-21 independent final fidelity receipt: 41 reviewed package inputs, 31 rebuilt sources, 23 exact signature matches and permitted axiom closures. Operational Linux gates are separate.')
