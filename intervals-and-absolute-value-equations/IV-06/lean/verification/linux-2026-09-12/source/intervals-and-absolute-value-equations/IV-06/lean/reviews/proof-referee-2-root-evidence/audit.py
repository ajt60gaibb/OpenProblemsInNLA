"""Root's independent final IV06 signature, axiom and primary-source receipt audit."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess

P = Path(__file__).resolve().parents[2]
O = Path(__file__).resolve().parent
D = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
fresh = json.loads((O / 'fresh-checks.json').read_text())
assert fresh['status'] == 'PASS' and len(fresh['commands']) == 6
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
assert config['theorem_names'] == ['NLA.IV06.' + n for n in solution]
assert config['definition_names'] == []
standard = {'propext', 'Classical.choice', 'Quot.sound'}
assert set(config['permitted_axioms']) == standard
sources = sorted((P / 'NLA/IV06').glob('*.lean')) + [P / 'Solution.lean']
safety = {}
for source in sources:
    text = source.read_text()
    code = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|run_tac)\b|import\s+Challenge', code), source
    safety[str(source.relative_to(P))] = {'sha256': sha(source), 'no_admissions_extra_trust_or_Challenge_import': True}
implementation = (O / 'NLA-IV06-Proof.log').read_text() + (O / 'Solution.log').read_text()
inspection_name = 'reviews-proof-referee-2-root-evidence-Inspect.log'
inspection = (O / inspection_name).read_text()
def axioms(text):
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
    for name, raw in rows:
        assert {x.strip() for x in raw.split(',') if x.strip()} == standard, name
    return [{'name': name, 'axioms': [x.strip() for x in raw.split(',')]} for name, raw in rows]
authored, independent = axioms(implementation), axioms(inspection)
assert len(authored) == 17 and len(independent) == 11
required = re.findall(r'^REQUIRED_DEPENDENCY_PRESENT (.+)$', inspection, re.M)
assert len(required) == 20 and len(set(required)) == 20
assert 'SAFE_PROJECT_DECLARATIONS_TRAVERSED 65' in inspection
assert 'PUBLIC_THEOREM_KINDS_VERIFIED 8' in inspection
exact = json.loads((O / 'independent-exact.json').read_text())
assert exact['definitions_sha256'] == sha(P / 'NLA/IV06/Definitions.lean')
assert exact['six_universal_nonnegative_distance_identities'] and exact['coefficient_identity']
certificate = (O / 'reviews-proof-referee-2-root-evidence-Certificate.log').read_text()
assert len(axioms(certificate)) == 1
assert '@of_decide_eq_true' in certificate and '@Eq.refl.{1} Bool Bool.true' in certificate
assert 'decide +kernel' in (O / 'Certificate.lean').read_text()

library = {}
for package, rel in [
    ('mathlib', 'Mathlib/LinearAlgebra/Matrix/ToLinearEquiv.lean'),
    ('mathlib', 'Mathlib/Topology/Connected/Clopen.lean'),
    ('mathlib', 'Mathlib/Topology/Order/IntermediateValue.lean'),
    ('mathlib', 'Mathlib/SetTheory/Cardinal/Order.lean'),
    ('leancert', 'LeanCert/Validity/DyadicBounds.lean'),
    ('leancert', 'LeanCert/Tactic/IntervalAuto/PointIneq.lean'),
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
          'fresh_check_sha256': sha(O / 'fresh-checks.json'), 'fresh_commands': 6,
          'proof_freeze_sha256': sha(P / 'verification/proof-freeze.json'),
          'frozen_project_inputs': 126, 'original_statement_inputs': 32, 'original_source_blobs': 8,
          'exact_export_headers': solution, 'source_safety': safety,
          'candidate_axioms': authored, 'candidate_explicit_kernel_checks': 17,
          'independent_axioms': independent, 'independent_explicit_kernel_checks': 12,
          'independent_retained_checker_axioms': axioms(certificate),
          'retained_checker_log_sha256': sha(O / 'reviews-proof-referee-2-root-evidence-Certificate.log'),
          'actual_inspection_sha256': sha(O / inspection_name), 'actual_required_dependencies': required,
          'safe_project_declarations': 65, 'independent_exact_sha256': sha(O / 'independent-exact.json'),
          'primary_and_rubric_inputs_sha256': sha(O / 'primary-library-and-rubric-inputs.json'),
          'candidate_change_or_failed_Lean_command': False,
          'numerical_certificate': 'Actual retained -18<0 helper, singleton [0,0], precision -53, depth10, independently repeated with decide +kernel; no interval subdivision.',
          'old_project_objects_excluded': True, 'dependency_artifacts_reused_read_only': True,
          'local_Lake_invocation': False, 'Linux_Comparator_run': False}
(O / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'fresh_commands': 6, 'candidate_kernel_checks': 17,
                  'independent_kernel_checks': 12, 'required_dependencies': len(required),
                  'audit_sha256': sha(O / 'audit.json')}))
