"""RA09 exact statement/source/helper/API audit, adapted from RA08 campaign checks.
Historical failed development diagnostics remain evidence, not implementation.
"""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
P=Path(__file__).resolve().parents[2]; E=Path(__file__).resolve().parent; W=P.parents[2]
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
f=json.loads((P/'reviews/statement-freeze.json').read_text())
for name,h in f['files'].items():assert sha(P/name)==h,name
for name,h in f['source_files'].items():
    raw=subprocess.check_output(['git','show',f['base']+':'+name],cwd=W)
    assert hashlib.sha256(raw).hexdigest()==h and (W/name).read_bytes()==raw,name
    assert subprocess.check_output(['git','rev-parse',f['base']+':'+name],cwd=W).decode().strip()==f['source_git_blobs'][name]

def inventory(rel):
    manifest=P/rel; data=json.loads(manifest.read_text()); rows=data['files']
    for name,item in rows.items():
        target=manifest.parent/name
        h=item if isinstance(item,str) else item['sha256']
        assert sha(target)==h,(rel,name)
        if isinstance(item,dict) and 'bytes' in item:assert target.stat().st_size==item['bytes'],(rel,name)
    actual={str(x.relative_to(manifest.parent)) for x in manifest.parent.rglob('*') if x.is_file() and x!=manifest}
    expected={k for k in rows if not k.startswith('../')}
    assert actual==expected,(rel,actual-expected,expected-actual)
    return {'path':rel,'sha256':sha(manifest),'bound_files':len(rows),'internal_files':len(actual),
            'complete_internal_inventory':True,'exact_outer_self_exclusion_only':True}

start=json.loads((P/'verification/proof-start.json').read_text())
review_inventories=[]
for row in start['reports']:
    assert sha(P/row['report'])==row['sha256']
    assert sha(P/row['complete_evidence_manifest'])==row['evidence_sha256']
    review_inventories.append(inventory(row['complete_evidence_manifest']))
helpers={
 'Frobenius':'f2d038d3d2f5195074ab5acc973771aaf57782d9ce9271c6fbc7132f8178c6ad',
 'Scalar':'be27edbd0f42e83fb825095bae65c48c8d90e8d1614ed90871abace1f55b6f17',
 'Harmonic':'629f355ef949d3f11acbba443fe1ba8a77d7ac89fb10e76f223ef5a47e7be91e',
 'ZeroColumn':'c5a21c431bc1118466097e9e761c9c95e113162c69379b397c8e76ec21038c00',
 'ZeroTail':'45ccfc67b7c59ce13d38d2822c69c36bd36519a9516798ca9d02074cb5e61dae'}
for name,h in helpers.items():assert sha(P/f'NLA/RA09/{name}.lean')==h,name
helper_inventories=[inventory('verification/'+n+'-development/EVIDENCE-MANIFEST.json') for n in
  ['frobenius','scalar','harmonic','zero-column','zero-tail']]
headers=lambda s:dict(re.findall(r'^theorem (\w+)(.*?):= by',s,re.M|re.S))
assert headers((P/'Challenge.lean').read_text())==headers((P/'Solution.lean').read_text())
names=['NLA.RA09.'+n for n in headers((P/'Solution.lean').read_text())]
config=json.loads((P/'comparator.json').read_text())
assert names==config['theorem_names'] and len(names)==17
assert config['definition_names']==[] and config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
code=[P/'Solution.lean',*sorted((P/'NLA/RA09').glob('*.lean'))]
for path in code:
    text=path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|run_tac)\b',text),path
    assert not re.search(r'^import\s+Challenge\b',text,re.M),path
    assert not re.search(r'set_option\s+leancert.trust\s+"(?!kernel")',text),path
apis=json.loads((P/'reviews/statement-evidence/primary-api-inputs.json').read_text())['sources']
extra=['mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean',
 'mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Restrict.lean',
 'mathlib/Mathlib/Order/Interval/Finset/Fin.lean',
 'mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean',
 'mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean']
pins={x['name']:x['rev'] for x in json.loads((P/'lake-manifest.json').read_text())['packages']}
for name in list(apis)+extra:
    package,rel=name.split('/',1);path=C/package/rel;rev=pins[package]
    raw=subprocess.check_output(['git','show',rev+':'+rel],cwd=C/package)
    assert path.read_bytes()==raw,name
    if name in apis:assert sha(path)==apis[name]['sha256'],name
    apis[name]={'sha256':sha(path),'bytes':len(raw),'commit':rev,
      'git_blob':subprocess.check_output(['git','rev-parse',rev+':'+rel],cwd=C/package).decode().strip(),
      'local_path':str(path)}
(E/'primary-api-inputs.json').write_text(json.dumps(apis,indent=2)+'\n')
checks=[]
for label,cmd in [
 ('permanent-ids-origin',['python3','tools/validate_problem_ids.py','--base-ref','origin/main']),
 ('permanent-ids-base',['python3','tools/validate_problem_ids.py','--base-ref',f['base']]),
 ('permanent-id-tests',['python3','-m','unittest','discover','-s','tests','-p','test_problem_ids.py','-v'])]:
    r=subprocess.run(cmd,cwd=W,capture_output=True);log=E/(label+'.log');log.write_bytes(r.stdout+r.stderr)
    assert r.returncode==0,log
    checks.append({'command':cmd,'exit_code':r.returncode,'log':log.name,'sha256':sha(log)})
assert not subprocess.check_output(['git','diff','--name-only'],cwd=W)
assert '**Status:** Solved' in (P.parent/'README.md').read_text()
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'phase':'Complete author source audit before two independent final mathematical reviews',
 'frozen_statement_inputs':len(f['files']),'original_source_Git_blobs':len(f['source_files']),
 'exact_reference_export_signatures':names,'definition_exceptions':[],
 'permitted_axioms':config['permitted_axioms'],'implementation_no_admissions_or_Challenge_import':True,
 'mathematical_inputs':{str(x.relative_to(P)):sha(x) for x in code},
 'sealed_helpers':helpers,'complete_helper_inventories':helper_inventories,
 'complete_statement_review_inventories':review_inventories,
 'API_manifest_sha256':sha(E/'primary-api-inputs.json'),
 'statement_gate_sha256':sha(P/'verification/proof-start.json'),
 'implementation_roles_sha256':sha(P/'verification/implementation-roles.json'),
 'repository_checks':checks,'tracked_diff_empty':True,
 'historical_wrapper_scope':'Frozen README/NUMERICAL_TARGETS/SourceCorrespondence retain the statement-stage context. Complete proof scope is documented separately; metadata installation follows independent final review.',
 'LeanCert_scope':'Actual kernel trust/axiom audits of pure exact proofs; no numerical interval or proof-oracle use.',
 'canonical_status':'Solved, unchanged','Linux_Comparator':'pending'}
(E/'source-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS',len(names),'exact signatures;',len(f['files']),'+',len(f['source_files']),'frozen inputs;',len(apis),'APIs')
