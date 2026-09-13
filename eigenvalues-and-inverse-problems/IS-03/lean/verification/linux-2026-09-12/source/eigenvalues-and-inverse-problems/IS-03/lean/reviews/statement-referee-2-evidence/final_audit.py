"""Independent read-only IS-03 statement, source, configuration and primary-API audit."""
from pathlib import Path
import hashlib, json, re, subprocess

out = Path(__file__).resolve().parent
project = out.parents[1]
repo = project.parents[2]
cache = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
git = lambda p, *args: subprocess.check_output(['git', '-C', str(p), *args])
write = lambda name, obj: (out/name).write_text(json.dumps(obj, indent=2)+'\n')

freeze_path = project/'reviews/statement-freeze.json'
assert sha(freeze_path) == '588196a54decb127a814dc4860621505d6874a077295f3e30a782d7f28b8ac6c'
assert sha(project/'reviews/statement-handoff.md') == '3c1d998ba3d3a658a7d9ea706e4357ab3587757050cef70e6f366481affd7c68'
freeze = json.loads(freeze_path.read_text())
for rel, expected in freeze['files'].items():
    assert sha(project/rel) == expected, rel
assert len(freeze['files']) == 34
sources = {}
for rel, expected in freeze['source_files'].items():
    assert sha(repo/rel) == expected, rel
    assert (repo/rel).read_bytes() == git(repo, 'show', freeze['base']+':'+rel), rel
    blob = git(repo, 'rev-parse', freeze['base']+':'+rel).decode().strip()
    assert blob == freeze['source_git_blobs'][rel], rel
    sources[rel] = {'sha256': expected, 'git_blob': blob}
assert len(sources) == 10
write('original-source-identity.json', {'base': freeze['base'], 'sources': sources})

assert not (project/'Solution.lean').exists()
assert not (project/'NLA/IS03/Proof.lean').exists()
defs = (project/'NLA/IS03/Definitions.lean').read_text()
stripped = re.sub(r'/\-.*?\-/', '', defs, flags=re.S)
assert not re.search(r'\b(axiom|sorry|admit|unsafe|native_decide|implemented_by|extern)\b', stripped)
assert not re.search(r'^\s*(instance|local instance|scoped instance|macro|elab|syntax)\b', stripped, re.M)
assert not re.search(r'\b(True|False)\b', stripped)
challenge = (project/'Challenge.lean').read_text()
names = re.findall(r'^theorem\s+(\w+)\b', challenge, re.M)
assert len(names) == 7 and challenge.count('  sorry\n') == 7
config = json.loads((project/'comparator.json').read_text())
assert config['theorem_names'] == ['NLA.IS03.'+name for name in names]
assert config['challenge_module'] == 'Challenge' and config['solution_module'] == 'Solution'
assert config['definition_names'] == []
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
raw = (out/'Inspect.log').read_text()
for required in ['Matrix.semiring', 'Matrix.trace', 'Matrix.charmatrix', 'Polynomial.derivative',
                 'Matrix.charpoly', 'Matrix.trace_eq_sum_roots_charpoly_of_splits',
                 'Matrix.aeval_self_charpoly', 'MvPolynomial.psum_eq_mul_esymm_sub_sum',
                 'sorryAx']:
    assert required in raw, required
write('statement-config.json', {
    'result': 'PASS', 'config': config,
    'definitions_sha256': sha(project/'NLA/IS03/Definitions.lean'),
    'Challenge_sha256': sha(project/'Challenge.lean'),
    'no_custom_matrix_polynomial_or_order_instances': True,
    'no_statement_implementation_exists': True,
    'scope': 'Seven admitted reference contracts. No proved target, certificate or Comparator invocation.'})

package_paths = {
    'mathlib': [
        'Mathlib/Data/Matrix/Mul.lean',
        'Mathlib/LinearAlgebra/Matrix/Trace.lean',
        'Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean',
        'Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean',
        'Mathlib/LinearAlgebra/Matrix/Charpoly/Eigs.lean',
        'Mathlib/Algebra/Polynomial/Derivative.lean',
        'Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean',
        'Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean'],
    'leancert': ['LeanCert/Tactic/Verification.lean']}
packages = json.loads((project/'lake-manifest.json').read_text())['packages']
pins = {p['name']: p['rev'] for p in packages}
assert len(pins) == 10
primary = {}
for package, paths in package_paths.items():
    package_root = cache/'.lake/packages'/package
    for rel in paths:
        assert (package_root/rel).read_bytes() == git(package_root, 'show', pins[package]+':'+rel), rel
        primary[package+'/'+rel] = {
            'sha256': sha(package_root/rel), 'revision': pins[package],
            'git_blob': git(package_root, 'rev-parse', pins[package]+':'+rel).decode().strip(),
            'matches_immutable_git_blob': True}
write('primary-library-inputs.json', primary)
for name, revision in pins.items():
    package_root = cache/'.lake/packages'/name
    assert git(package_root, 'rev-parse', 'HEAD').decode().strip() == revision, name
    assert not git(package_root, 'status', '--porcelain=v1').strip(), name

standards = Path('/tmp/nla-lean-formalization/standards')
standards_manifest = json.loads((standards/'MANIFEST.json').read_text())
rubrics = {}
for angle in ['scope', 'correctness', 'proof-quality', 'reuse', 'generality',
              'api-design', 'naming', 'placement', 'documentation', 'attribution']:
    rel = 'sources/TauCetiProject/TauCetiReview/rubrics/'+angle+'.md'
    assert sha(standards/rel) == standards_manifest[rel]['sha256'], rel
    rubrics[angle] = standards_manifest[rel]
write('review-standard-inputs.json', {
    'pinned_Tau_Ceti_revision': 'afb424eda89e8ac96d9eb69f6a88972055a4cd1b',
    'rubrics': rubrics, 'NLA_adaptation_sha256': sha(repo/'docs/lean/REVIEW.md'),
    'scope': 'Independent AI statement review through the repository adaptation, not an official Tau Ceti review.'})

search = ['rg', '-n', 'trace.*pow|pow.*trace|trace_eq_sum_roots|trace_eq_neg_charpoly_coeff|charpoly_fromBlocks|charpoly_reindex|aeval_self_charpoly|pow_eq_aeval_mod_charpoly|psum_eq_mul_esymm_sub_sum|aeval_esymm_eq_multiset_esymm|coeff_derivative|mul_nonneg|pow_nonneg',
          '.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix',
          '.lake/packages/mathlib/Mathlib/Data/Matrix',
          '.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Derivative.lean',
          '.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/Symmetric']
result = subprocess.run(search, cwd=cache, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert result.returncode == 0
(out/'reuse-search.log').write_bytes(result.stdout)
write('reuse-search.json', {
    'command': search, 'exit_code': result.returncode, 'log_sha256': sha(out/'reuse-search.log'),
    'assessment': 'Actual block-charpoly, trace/coefficient, Cayley-Hamilton and symmetric-function Newton APIs exist. The generic trace-power bridge is still a proof obligation; a companion calculation or trace-only roots lemma cannot substitute for it.'})
assert json.loads((out/'fresh-result.json').read_text())['result'] == 'PASS'
assert json.loads((out/'reconstruction.json').read_text())['result'] == 'PASS'
write('integrity-after.json', {
    'result': 'PASS', 'frozen_project_inputs_unchanged': len(freeze['files']),
    'original_source_git_blobs_unchanged': len(sources), 'dependency_sources_clean': len(pins),
    'primary_library_files_bound': len(primary), 'fresh_statement_commands': 3,
    'definition_kernel_assertions': 8, 'Challenge_holes': 7,
    'no_frozen_source_or_mathematical_edits': True, 'publication_or_Linux_claim': False,
    'files': {rel: sha(project/rel) for rel in freeze['files']}})
print('PASS: all 34 frozen project inputs and 10 original source Git blobs unchanged; 7 configured contracts; 10 clean pins; 9 primary-library source files')
