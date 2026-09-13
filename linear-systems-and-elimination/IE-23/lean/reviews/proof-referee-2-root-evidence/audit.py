"""Root's independent final IE23 signature, axiom and primary-source receipt audit."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess

P = Path(__file__).resolve().parents[2]
O = Path(__file__).resolve().parent
D = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
fresh = json.loads((O / 'fresh-checks.json').read_text())
assert fresh['status'] == 'PASS' and len(fresh['commands']) == 10
for c in fresh['commands']:
    assert c['exit_code'] == 0 and sha(P / c['source']) == c['source_sha256']
    assert sha(O / c['log']) == c['log_sha256']

def headers(file):
    result = {}
    for m in re.finditer(r'^theorem\s+(\w+)\b(.*?):=\s*by', file.read_text(), re.M | re.S):
        result[m[1]] = ' '.join((m[1] + m[2]).split())
    return result

challenge, solution = headers(P / 'Challenge.lean'), headers(P / 'Solution.lean')
assert challenge == solution and len(solution) == 8
config = json.loads((P / 'comparator.json').read_text())
assert config['theorem_names'] == ['NLA.IE23.' + n for n in solution]
assert config['definition_names'] == []
standard = {'propext', 'Classical.choice', 'Quot.sound'}
assert set(config['permitted_axioms']) == standard
sources = sorted((P / 'NLA/IE23').glob('*.lean')) + [P / 'Solution.lean']
safety = {}
for source in sources:
    text = source.read_text()
    code = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|run_tac)\b|import\s+Challenge', code), source
    safety[str(source.relative_to(P))] = {'sha256': sha(source), 'no_admissions_extra_trust_or_Challenge_import': True}
implementation = (O / 'NLA-IE23-Proof.log').read_text() + (O / 'Solution.log').read_text()
inspection_name = 'reviews-proof-referee-2-root-evidence-Inspect.log'
inspection = (O / inspection_name).read_text()
def axioms(text):
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
    for name, raw in rows:
        assert {x.strip() for x in raw.split(',') if x.strip()} == standard, name
    return [{'name': name, 'axioms': [x.strip() for x in raw.split(',')]} for name, raw in rows]
authored, independent = axioms(implementation), axioms(inspection)
assert len(authored) == 16 and len(independent) == 12
required = re.findall(r'^REQUIRED_DEPENDENCY_PRESENT (.+)$', inspection, re.M)
assert len(required) == 28 and len(set(required)) == 28
assert 'SAFE_PROJECT_DECLARATIONS_TRAVERSED 93' in inspection
assert 'PUBLIC_THEOREM_KINDS_VERIFIED 8' in inspection
exact = json.loads((O / 'independent-exact.json').read_text())
assert exact['source_sha256'] == sha(P / 'NLA/IE23/Definitions.lean')
assert exact['universal_quartic_SOS'] and exact['all_complex_action_Gram_identity']

library = {}
for package, rel in [
    ('mathlib', 'Mathlib/Analysis/InnerProductSpace/PiL2.lean'),
    ('mathlib', 'Mathlib/Analysis/SpecialFunctions/Pow/Real.lean'),
    ('mathlib', 'Mathlib/LinearAlgebra/Matrix/Rank.lean'),
    ('mathlib', 'Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean'),
    ('mathlib', 'Mathlib/Order/ConditionallyCompleteLattice/Basic.lean'),
    ('leancert', 'LeanCert/Tactic/Verification.lean')]:
    root = D / package
    pin = next(x['revision'] for x in fresh['pins_before'] if x['name'] == package)
    blob = subprocess.check_output(['git', 'show', pin + ':' + rel], cwd=root)
    assert blob == (root / rel).read_bytes()
    library[package + '/' + rel] = {'revision': pin, 'sha256': sha(root / rel), 'matches_pinned_Git_blob': True}
rubric_root = Path('/tmp/nla-lean-formalization/standards/sources/TauCetiProject/TauCetiReview/rubrics')
rubric_reference = json.loads(Path('/tmp/nla-lean-mi03-worktree/matrix-inequalities-and-norms/MI-03/lean/reviews/proof-referee-1-evidence/rubric-inputs.json').read_text())
rubrics = {}
for relative, expected in rubric_reference['rubrics'].items():
    f = rubric_root / Path(relative).name
    assert sha(f) == expected['sha256'] and f.stat().st_size == expected['bytes']
    rubrics[f.name] = expected
assert len(rubrics) == 10
inputs = {'primary_library': library, 'TauCeti_commit': rubric_reference['commit'], 'rubrics': rubrics,
          'NLA_adaptation_sha256': sha(P.parents[2] / 'docs/lean/REVIEW.md'),
          'scope': 'Independent AI application; not an official Tau Ceti service or endorsement'}
(O / 'primary-library-and-rubric-inputs.json').write_text(json.dumps(inputs, indent=2) + '\n')
result = {'verdict': 'PASS independent local final proof review; actual Linux still pending',
          'reviewer': '/root', 'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'fresh_check_sha256': sha(O / 'fresh-checks.json'), 'fresh_commands': 10,
          'proof_freeze_sha256': sha(P / 'reviews/proof-freeze.json'),
          'frozen_project_inputs': 104, 'original_statement_inputs': 32, 'original_source_blobs': 8,
          'exact_export_headers': solution, 'source_safety': safety,
          'candidate_axioms': authored, 'candidate_explicit_kernel_checks': 16,
          'independent_axioms': independent, 'independent_explicit_kernel_checks': 12,
          'actual_inspection_sha256': sha(O / inspection_name), 'actual_required_dependencies': required,
          'safe_project_declarations': 93, 'independent_exact_sha256': sha(O / 'independent-exact.json'),
          'primary_and_rubric_inputs_sha256': sha(O / 'primary-library-and-rubric-inputs.json'),
          'initial_driver_correction': 'Before any Lean invocation, supported the original statement manifest string-valued hashes as well as the final manifest objects. No source change or Lean failure.',
          'old_project_objects_excluded': True, 'dependency_artifacts_reused_read_only': True,
          'local_Lake_invocation': False, 'Linux_Comparator_run': False}
(O / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'fresh_commands': 10, 'candidate_kernel_checks': 16,
                  'independent_kernel_checks': 12, 'required_dependencies': len(required),
                  'audit_sha256': sha(O / 'audit.json')}))
