"""Bind exact RA08 statements, mathematical sources, helpers, exports and primary APIs."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
P=Path(__file__).resolve().parents[2]
E=Path(__file__).resolve().parent
W=P.parents[2]
C=Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
f=json.loads((P/'reviews/statement-freeze.json').read_text())
for name,h in f['files'].items(): assert sha(P/name)==h,name
for name,h in f['source_files'].items():
    raw=subprocess.check_output(['git','show',f['base']+':'+name],cwd=W)
    assert hashlib.sha256(raw).hexdigest()==h and (W/name).read_bytes()==raw,name
start=json.loads((P/'verification/proof-start.json').read_text())
for name,h in start['reports'].items(): assert sha(P/name)==h,name
for name,item in start['evidence'].items(): assert sha(P/name)==item['sha256'],name
helpers={'NLA/RA08/OrderedExistence.lean':'4da2bb55befc17bca7d520fbae186aafede693927bcb2768e810790a0a3de37b',
 'NLA/RA08/Spectral.lean':'8b700ff01b12e8d37c330ebbdb799a61af766483606e1870f555a6d182ca8833',
 'NLA/RA08/SpectralCFC.lean':'df90bbcab9837df4b0c51de0a98de4795745b204b1f58ab7690e4707ab0d59d6'}
for name,h in helpers.items(): assert sha(P/name)==h,name
headers=lambda s:dict(re.findall(r'^theorem (\w+)(.*?):= by',s,re.M|re.S))
assert headers((P/'Challenge.lean').read_text())==headers((P/'Solution.lean').read_text())
names=['NLA.RA08.'+n for n in headers((P/'Solution.lean').read_text())]
config=json.loads((P/'comparator.json').read_text())
assert names==config['theorem_names'] and len(names)==14
assert config['definition_names']==[]
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
code=[P/'Solution.lean',*sorted((P/'NLA/RA08').glob('*.lean'))]
for path in code:
    text=path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|run_tac)\b',text),path
    assert not re.search(r'^import\s+Challenge\b',text,re.M),path
    assert not re.search(r'set_option\s+leancert.trust\s+"(?!kernel")',text),path
apis=json.loads((P/'reviews/statement-evidence/API-SOURCE-INPUTS.json').read_text())
extra=[
 'mathlib/Mathlib/Analysis/Matrix/Normed.lean',
 'mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean',
 'mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Restrict.lean',
 'mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean',
 'mathlib/Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean',
 'mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean',
 'mathlib/Mathlib/Order/Fin/Basic.lean',
 'leancert/LeanCert/Validity/DyadicBounds.lean']
pins={x['name']:x['rev'] for x in json.loads((P/'lake-manifest.json').read_text())['packages']}
for name in extra:
    package,rel=name.split('/',1);path=C/package/rel;rev=pins[package]
    raw=subprocess.check_output(['git','show',rev+':'+rel],cwd=C/package)
    assert path.read_bytes()==raw,name
    apis[name]={'sha256':sha(path),'bytes':len(raw),'commit':rev,
      'git_blob':subprocess.check_output(['git','rev-parse',rev+':'+rel],cwd=C/package).decode().strip()}
for name,item in apis.items():
    package,rel=name.split('/',1)
    path=W/rel if package=='repository' else C/package/rel
    assert sha(path)==item['sha256'],name
(E/'API-SOURCE-INPUTS.json').write_text(json.dumps(apis,indent=2)+'\n')
checks=[]
for label,cmd in [
 ('permanent-ids-origin',['python3','tools/validate_problem_ids.py','--base-ref','origin/main']),
 ('permanent-ids-source-base',['python3','tools/validate_problem_ids.py','--base-ref',f['base']]),
 ('permanent-id-tests',['python3','-m','unittest','discover','-s','tests','-p','test_problem_ids.py','-v'])]:
    r=subprocess.run(cmd,cwd=W,capture_output=True)
    log=E/(label+'.log');log.write_bytes(r.stdout+r.stderr)
    assert r.returncode==0,log
    checks.append({'command':cmd,'exit_code':r.returncode,'log':log.name,'sha256':sha(log)})
assert not subprocess.check_output(['git','diff','--name-only'],cwd=W)
assert '**Status:** Solved' in (P.parent/'README.md').read_text()
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'phase':'Complete source audit before independent final mathematical review',
 'frozen_statement_inputs':len(f['files']),'original_source_Git_blobs':len(f['source_files']),
 'exact_reference_export_signatures':names,'definition_exceptions':[],
 'permitted_axioms':config['permitted_axioms'],'implementation_no_admissions_or_Challenge_import':True,
 'mathematical_inputs':{str(x.relative_to(P)):sha(x) for x in code},
 'helper_inputs':helpers,'API_manifest_sha256':sha(E/'API-SOURCE-INPUTS.json'),
 'statement_gate_sha256':sha(P/'verification/proof-start.json'),
 'implementation_roles_sha256':sha(P/'verification/implementation-roles.json'),
 'repository_checks':checks,'tracked_diff_empty':True,
 'historical_frozen_wrapper_scope':'README and formalization.yaml still record statement stage; completed proof scope is recorded separately pending final review and candidate packaging.',
 'canonical_status':'Solved, unchanged','Linux_Comparator':'pending'}
(E/'source-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS',len(names),'exact signatures;',len(f['files']),'+',len(f['source_files']),'frozen inputs')
