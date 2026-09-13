"""Bind original sources, actual compiled inputs, exact contracts and clean pins before freezing."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import tomllib

P = Path(__file__).resolve().parents[2]
E = Path(__file__).resolve().parent
W = P.parents[2]
BASE = 'f41f1f9ffa2171550d4bb795862c6170c4f26070'
M = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages/mathlib')


def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()


def sha(f):
    return sha_bytes(Path(f).read_bytes())


source_paths = [
    'eigenvalues-and-inverse-problems/IS-03/README.md',
    'eigenvalues-and-inverse-problems/IS-03/problem.tex',
    'eigenvalues-and-inverse-problems/IS-03/solution.md',
    'eigenvalues-and-inverse-problems/IS-03/solution.tex',
    'references/colbrook-additional-2026-09-11/original-manuscripts/IS-03.md',
    'references/colbrook-additional-2026-09-11/verification/reviews/IS-03-review.md',
    'references/colbrook-additional-2026-09-11/README.md',
    'references/colbrook-additional-2026-09-11/original-manuscripts/README.md',
    'references/colbrook-additional-2026-09-11/proof-hashes.json',
    'references/colbrook-additional-2026-09-11/verification/check_additional_results.py']
sources = {}
for path in source_paths:
    blob = subprocess.check_output(['git', 'show', f'{BASE}:{path}'], cwd=W)
    local = (W / path).read_bytes()
    assert local == blob, path
    sources[path] = {'bytes': len(blob), 'sha256': sha_bytes(blob),
                     'git_blob': subprocess.check_output(['git', 'rev-parse', f'{BASE}:{path}'], cwd=W).decode().strip()}
original = sources[source_paths[4]]
assert original['sha256'] == '548553e2f177da2a2c5135030c6a34fff761d2b9c800b246b7f9a6797e02d45c'
assert original['bytes'] == 5068
(P / 'source-inputs.json').write_text(json.dumps({
    'base': BASE, 'sources': sources,
    'read_scope': ('Complete canonical target, problem TeX, both authored textual solution formats, '
                   'original manuscript, informal review, submission/preservation metadata and '
                   'hash record; only the IS03 function of the multi-problem diagnostic is relevant. '
                   'No PDF visual review or new literature/priority claim at this stage.')}, indent=2) + '\n')

library_paths = [
    'Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean',
    'Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean',
    'Mathlib/LinearAlgebra/Matrix/Charpoly/Eigs.lean',
    'Mathlib/LinearAlgebra/Matrix/Trace.lean',
    'Mathlib/LinearAlgebra/Matrix/Notation.lean',
    'Mathlib/Algebra/Polynomial/Derivative.lean',
    'Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean',
    'Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean',
    'Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean']
libraries = {}
rev = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=M).decode().strip()
assert rev == '0df444a360eaa60ab8c11dca51a86af692955474'
for path in library_paths:
    b = subprocess.check_output(['git', 'show', f'{rev}:{path}'], cwd=M)
    assert b == (M / path).read_bytes()
    libraries[path] = {'bytes': len(b), 'sha256': sha_bytes(b)}
(E / 'API-SOURCE-INPUTS.json').write_text(json.dumps({'mathlib': rev,
    'scope': 'Pinned source identity for relevant definitions, interfaces and implementation sections inspected; API_NOTES states unproved bridges.',
    'files': libraries}, indent=2) + '\n')

challenge = (P / 'Challenge.lean').read_text()
definitions = (P / 'NLA/IS03/Definitions.lean').read_text()
names = ['NLA.IS03.' + n for n in re.findall(r'^theorem (\w+)', challenge, re.M)]
assert len(names) == 7 and len(re.findall(r'^\s+sorry\s*$', challenge, re.M)) == 7
assert not re.search(r'\b(sorry|axiom|native_decide|run_tac|unsafe)\b', definitions)
assert not (P / 'Solution.lean').exists() and not (P / 'NLA/IS03/Proof.lean').exists()
config = json.loads((P / 'comparator.json').read_text())
assert config == {'challenge_module': 'Challenge', 'solution_module': 'Solution',
                  'theorem_names': names, 'definition_names': [],
                  'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound']}
lake = tomllib.loads((P / 'lakefile.toml').read_text())
assert lake['defaultTargets'] == ['Challenge']
assert [lib['name'] for lib in lake['lean_lib']] == ['NLA', 'Challenge', 'Solution']
assert lake['require'][0]['rev'] == '621a43d7cf21f87872392a01e874f2f1dbddc926'
latest = json.loads((E / 'latest.json').read_text())
run = Path(latest['attempt'])
result = json.loads((run / 'result.json').read_text())
assert sha(run / 'result.json') == latest['result_sha256']
assert len(result['commands']) == 3 and result['pins_rechecked_after']
for command in result['commands']:
    assert command['exit_code'] == 0
    assert sha(P / command['source']) == command['source_sha256']
    assert sha(run / command['log']) == command['log_sha256']
assert not (run / 'NLA-IS03-Definitions.log').read_bytes()
challenge_log = (run / 'Challenge.log').read_text()
assert challenge_log.count('warning: declaration uses `sorry`') == 7
assert 'error' not in challenge_log
inspection = (run / 'reviews-statement-evidence-Inspect.log').read_text()
assert 'warning:' not in inspection and 'error:' not in inspection
assert inspection.count('depends on axioms:') == 3
for item in ['Matrix.semiring', 'Matrix.trace', 'Matrix.charpoly',
             'Polynomial.derivative', 'MvPolynomial.psum_eq_mul_esymm_sub_sum']:
    assert item in inspection
diagnostic = json.loads((E / 'exact-checks.json').read_text())
assert diagnostic['source_sha256'] == sha(P / 'NLA/IS03/Definitions.lean')
assert diagnostic['newton_moments_1_to_7'] == diagnostic['companion_trace_moments_1_to_7']

checks = []
for label, cmd in [
    ('permanent-ids', ['python3', 'tools/validate_problem_ids.py', '--base-ref', 'origin/main']),
    ('permanent-id-tests', ['python3', '-m', 'unittest', 'discover', '-s', 'tests', '-p', 'test_problem_ids.py', '-v'])]:
    r = subprocess.run(cmd, cwd=W, capture_output=True)
    log = E / (label + '.log')
    log.write_bytes(r.stdout + r.stderr)
    assert r.returncode == 0, (cmd, log)
    checks.append({'command': cmd, 'exit_code': r.returncode, 'log': log.name, 'log_sha256': sha(log)})
status = subprocess.check_output(['git', 'status', '--porcelain=v1'], cwd=W)
assert status.decode().strip() == '?? eigenvalues-and-inverse-problems/IS-03/lean/'
(E / 'worktree-status.log').write_bytes(status)
assert '**Status:** Solved' in (W / source_paths[0]).read_text()
assert not subprocess.check_output(['git', 'diff', '--name-only'], cwd=W)
record = {
    'phase': 'statement-only-before-independent-review',
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'base': BASE, 'branch': subprocess.check_output(['git', 'branch', '--show-current'], cwd=W).decode().strip(),
    'source_count': len(sources), 'source_manifest_sha256': sha(P / 'source-inputs.json'),
    'mathlib_source_inputs_sha256': sha(E / 'API-SOURCE-INPUTS.json'),
    'fresh_result_sha256': sha(run / 'result.json'), 'exact_diagnostic_sha256': sha(E / 'exact-checks.json'),
    'theorem_names': names, 'seven_intended_holes_only': True, 'no_proof_or_solution': True,
    'comparator_sha256': sha(P / 'comparator.json'), 'default_target': 'Challenge',
    'future_solution_library_registered': True, 'definition_exceptions': [],
    'permitted_axioms': config['permitted_axioms'],
    'canonical_status': 'Solved, unchanged', 'tracked_diff_empty': True,
    'repository_checks': checks,
    'scope': 'Author integrity and statement checks. No independent approval, complete Lean proof, LeanCert numeric certificate or Linux Comparator result is asserted.'}
(E / 'input-audit.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
