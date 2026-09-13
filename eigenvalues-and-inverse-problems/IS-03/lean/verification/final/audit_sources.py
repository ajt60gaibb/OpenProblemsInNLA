"""Preserve exact reviewed boundaries, external APIs, and solution export signatures."""
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
helper=json.loads((P/'verification/newton-helper-handoff.json').read_text())
assert sha(P/'NLA/IS03/Newton.lean')=='451953080999a9b7aec73af27af178018fec6d340439c3b4081716165a7f1ddd'

def headers(source):
    return dict(re.findall(r'^theorem (\w+)(.*?):= by',source,re.M|re.S))
challenge=(P/'Challenge.lean').read_text()
solution=(P/'Solution.lean').read_text()
assert headers(challenge)==headers(solution)
names=['NLA.IS03.'+n for n in headers(solution)]
config=json.loads((P/'comparator.json').read_text())
assert names==config['theorem_names'] and len(names)==7
assert config['definition_names']==[]
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
code=[P/'Solution.lean',*(P/'NLA/IS03').glob('*.lean')]
for path in code:
    text=path.read_text()
    assert not re.search(r'\b(sorry|axiom|native_decide|unsafe|run_tac)\b',text),path
    assert not re.search(r'^import\s+Challenge\b',text,re.M),path

apis=[
 'Mathlib/Data/Matrix/Mul.lean',
 'Mathlib/Data/Matrix/Basic.lean',
 'Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean',
 'Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean',
 'Mathlib/LinearAlgebra/Matrix/ToLin.lean',
 'Mathlib/LinearAlgebra/Charpoly/ToMatrix.lean',
 'Mathlib/LinearAlgebra/Matrix/Trace.lean',
 'Mathlib/LinearAlgebra/Trace.lean',
 'Mathlib/LinearAlgebra/Eigenspace/Basic.lean',
 'Mathlib/LinearAlgebra/Eigenspace/Charpoly.lean',
 'Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean',
 'Mathlib/FieldTheory/Separable.lean',
 'Mathlib/Analysis/Complex/Polynomial/Basic.lean',
 'Mathlib/Algebra/Polynomial/Roots.lean',
 'Mathlib/Algebra/Polynomial/AlgebraMap.lean',
 'Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean',
 'Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean',
 'Mathlib/RingTheory/Polynomial/Vieta.lean']
libraries={}
for name in apis:
    path=C/'mathlib'/name
    raw=subprocess.check_output(['git','show','0df444a360eaa60ab8c11dca51a86af692955474:'+name],cwd=C/'mathlib')
    assert path.read_bytes()==raw,name
    libraries[name]={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
(E/'API-SOURCE-INPUTS.json').write_text(json.dumps({'pin':'0df444a360eaa60ab8c11dca51a86af692955474',
    'scope':'Pinned source identities for definitions and implementation sections inspected; PROOF_MAP explains the actual retained uses.',
    'files':libraries},indent=2)+'\n')
commands=[]
for label,cmd in [
    ('permanent-ids',['python3','tools/validate_problem_ids.py','--base-ref','origin/main']),
    ('permanent-id-tests',['python3','-m','unittest','discover','-s','tests','-p','test_problem_ids.py','-v'])]:
    r=subprocess.run(cmd,cwd=W,capture_output=True)
    log=E/(label+'.log');log.write_bytes(r.stdout+r.stderr)
    assert r.returncode==0,log
    commands.append({'command':cmd,'exit_code':r.returncode,'log':log.name,'sha256':sha(log)})
assert not subprocess.check_output(['git','diff','--name-only'],cwd=W)
assert '**Status:** Solved' in (P.parent/'README.md').read_text()
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'phase':'Author complete-source audit before independent final review',
    'frozen_statement_inputs':len(f['files']),'original_source_blobs':len(f['source_files']),
    'exact_export_signatures':names,'empty_definition_exceptions':True,
    'permitted_axioms':config['permitted_axioms'],
    'solution_has_no_Challenge_import_or_admissions':True,
    'mathematical_sources':{str(x.relative_to(P)):sha(x) for x in sorted(code)},
    'API_manifest_sha256':sha(E/'API-SOURCE-INPUTS.json'),
    'proof_gate_sha256':sha(P/'verification/proof-start.json'),
    'newton_helper_handoff_sha256':sha(P/'verification/newton-helper-handoff.json'),
    'repository_checks':commands,'tracked_diff_empty':True,
    'canonical_status':'Solved, unchanged','Linux_Comparator':'pending'}
(E/'source-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS',len(names),'exact exports;',len(f['files']),'+',len(f['source_files']),'frozen inputs preserved')
