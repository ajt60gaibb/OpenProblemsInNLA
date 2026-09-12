"""Bind the independent MI-22 statement review, finite checks and actual APIs."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def save(name, data): (OUT / name).write_text(json.dumps(data, indent=2) + '\n')


freeze = json.loads((PROJECT / 'reviews/statement-freeze.json').read_text())
for rel, h in freeze['files'].items(): assert sha(PROJECT / rel) == h, rel
for rel, h in freeze['source_files'].items(): assert sha(REPO / rel) == h, rel
assert not (PROJECT / 'Solution.lean').exists() and not (PROJECT / 'NLA/MI22/Proof.lean').exists()
text = (PROJECT / 'Challenge.lean').read_text()
names = ['NLA.MI22.' + n for n in re.findall(r'^theorem (\w+)', text, re.M)]
config = json.loads((PROJECT / 'comparator.json').read_text())
assert len(names) == 8 and names == config['theorem_names']
assert config['definition_names'] == []
assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert len(re.findall(r'^\s+sorry\s*$', text, re.M)) == 8
headers = {m.group(1): text[m.start():text.index(':= by', m.start())]
           for m in re.finditer(r'^theorem (\w+)', text, re.M)}
save('signatures.json', {'count': 8, 'exact_headers': headers, 'comparator': config,
                        'scope': 'Frozen statement signatures only; no proof completion or Linux Comparator claim.'})

inspection = (OUT / 'inspection.log').read_text()
required = ['@CFC.rpow', '@Matrix.instPartialOrder Complex',
            '@LinearMap.singularValues Complex', '(EuclideanSpace Complex (Fin n))',
            '@Matrix.toEuclideanCLM Complex (Fin n)', 'Complex.normSq',
            'Finset.range k', '@NLA.MI22.singularPrefix n X n',
            '@NLA.MI22.singularPrefix n Y n', 'NLA.MI22.witnessB',
            'NLA.MI22.witnessRoot', 'Matrix.semiring',
            'LinearMap.singularValues_fin', 'CFC.rpow_add']
for item in required: assert item in inspection, item
save('semantic-checks.json', {'actual_environment_tokens_checked': required,
                             'eight_quantified_signatures_inspected': True,
                             'all_witness_and_norm_bridges_are_conclusions': True,
                             'no_implementation_present': True,
                             'verdict': 'PASS for statement gate'})

proc = subprocess.run(['python3', str(OUT / 'reconstruct.py')], cwd=PROJECT,
                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(OUT / 'reconstruction.log').write_bytes(proc.stdout)
assert proc.returncode == 0, proc.stdout.decode()
data = json.loads((OUT / 'reconstruction.json').read_text())
assert data['verdict'] == 'PASS' and data['adapted_B_differs_from_printed_integer_B']

libraries = {
    'mathlib': ['Mathlib/Analysis/InnerProductSpace/SingularValues.lean',
                'Mathlib/Analysis/InnerProductSpace/Spectrum.lean',
                'Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean',
                'Mathlib/Analysis/Matrix/Order.lean',
                'Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean',
                'Mathlib/Analysis/CStarAlgebra/Matrix.lean',
                'Mathlib/Analysis/CStarAlgebra/Basic.lean'],
    'leancert': ['LeanCert/Tactic/Verification.lean']
}
save('library-sources.json', {package: {
    'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PROJECT / '.lake/packages' / package).decode().strip(),
    'files': {rel: sha(PROJECT / '.lake/packages' / package / rel) for rel in files}
} for package, files in libraries.items()})

queries = [
    ['rg', '-n', 'singularValues_fin|singularValues_antitone|singularValues_of_finrank_le|singularValues.*norm|norm.*singularValues', '.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/SingularValues.lean'],
    ['rg', '-n', 'eigenvalues_antitone|eigenvectorBasis|norm_pow_two_pow|l2_opNorm_toEuclideanCLM|l2_opNorm_diagonal|cfc_eq|rpow_eq_cfc_real|rpow_rpow',
     '.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean',
     '.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Basic.lean',
     '.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Matrix.lean',
     '.lake/packages/mathlib/Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean',
     '.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean'],
]
records = []
for i, command in enumerate(queries, 1):
    proc = subprocess.run(command, cwd=PROJECT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    name = f'library-search-{i}.log'; (OUT / name).write_bytes(proc.stdout)
    assert proc.returncode == 0
    records.append({'command': command, 'exit_code': proc.returncode, 'log': name, 'log_sha256': sha(OUT / name)})
save('library-searches.json', records)
save('primary-source-check.json', {
    'url': 'https://arxiv.org/pdf/2105.13356', 'version': '2105.13356v1',
    'accessed_utc_date': '2026-09-12', 'printed_pages_checked': [1, 2, 3],
    'method': 'Read the actual primary PDF through web PDF text extraction; no visual-page or new literature-status audit claimed.',
    'observations': ['Complex matrices and positive modulus define descending singular values.',
                     'Log-majorization includes equality of the full product; its weak variant is different.',
                     'The weighted-mean factor order and Conjecture 1.1 match the retained canonical positive-definite target.',
                     'The paper states a broader semidefinite domain. The adapted strictly positive-definite witness lies inside it; no regularization theorem is claimed here.']
})

standards = Path('/tmp/nla-lean-formalization/standards')
tree_path = standards / 'TauCetiProject_TauCetiReview-tree.json'
commit_path = standards / 'TauCetiProject_TauCetiReview-commit.json'
tree = json.loads(tree_path.read_text())
commit = json.loads(commit_path.read_text())['sha']
assert commit == 'afb424eda89e8ac96d9eb69f6a88972055a4cd1b'
blobs = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
rubrics = {}
for name in ['correctness.md', 'scope.md', 'proof-quality.md', 'generality.md', 'reuse.md', 'attribution.md']:
    path = standards / 'sources/TauCetiProject/TauCetiReview/rubrics' / name
    b = path.read_bytes(); blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
    assert blobs['rubrics/' + name] == blob
    rubrics[name] = {'sha256': sha(path), 'git_blob_sha1': blob}
save('review-standards.json', {'revision': commit, 'reused_reviewed_rubric_bytes': rubrics,
                              'cached_tree_sha256': sha(tree_path), 'cached_commit_sha256': sha(commit_path),
                              'local_adaptation_sha256': sha(REPO / 'docs/lean/REVIEW.md'),
                              'scope': 'Applicable NLA statement-fidelity adaptation, not official Tau Ceti endorsement or review service.'})
save('integrity.json', {'all_27_frozen_project_inputs_unchanged': True,
                        'all_eight_original_source_inputs_unchanged': True,
                        'tracked_diff': subprocess.check_output(['git', 'diff', '--name-only'], cwd=REPO).decode(),
                        'staged_diff': subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=REPO).decode(),
                        'reviewer_writes': ['reviews/statement-referee-1.md', 'reviews/statement-referee-1-evidence/'],
                        'no_proof_implementation_or_publication_performed': True})
print('PASS: eight exact statement exports, actual complex CFC/singular/norm semantics, independent exact adaptation, no proof or changed frozen input.')
