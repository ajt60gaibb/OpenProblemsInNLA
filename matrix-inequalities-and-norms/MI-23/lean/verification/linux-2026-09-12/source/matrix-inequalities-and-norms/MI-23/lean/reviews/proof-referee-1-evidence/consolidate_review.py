"""Bind the independent MI-23 review's exact signatures, static scope and sources."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def save(name, data):
    (OUT / name).write_text(json.dumps(data, indent=2) + '\n')


def headers(path):
    text = path.read_text()
    return {m.group(1): text[m.start():text.index(':= by', m.start())]
            for m in re.finditer(r'^theorem ([A-Za-z0-9_]+)\b', text, re.M)}


challenge = headers(PROJECT / 'Challenge.lean')
solution = headers(PROJECT / 'Solution.lean')
config = json.loads((PROJECT / 'comparator.json').read_text())
assert len(challenge) == len(solution) == 8
assert challenge == solution
assert config['theorem_names'] == ['NLA.MI23.' + name for name in challenge]
assert config['definition_names'] == []
assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
save('signatures.json', {'comparison': 'Literal theorem headers through but excluding := by; no whitespace normalization.',
                        'count': 8, 'headers': challenge, 'comparator': config, 'verdict': 'PASS'})

freeze = json.loads((PROJECT / 'reviews/proof-freeze.json').read_text())
oldfreeze = json.loads((PROJECT / 'reviews/statement-freeze.json').read_text())
assert len(freeze['files']) == 25
for rel, rec in freeze['files'].items():
    assert sha(PROJECT / rel) == rec['sha256'] and (PROJECT / rel).stat().st_size == rec['bytes'], rel
oldchanges = [rel for rel, rec in oldfreeze['files'].items() if sha(PROJECT / rel) != rec['sha256']]
assert set(oldchanges) == {'README.md', 'lakefile.toml'}
gate = json.loads((PROJECT / 'reviews/implementation-gate.json').read_text())
for rel, h in {**gate['statement_sha256'], **gate['reviews']}.items():
    assert sha(PROJECT / rel) == h, rel

impl = [PROJECT / 'Solution.lean', *sorted((PROJECT / 'NLA/MI23').glob('*.lean'))]
for path in impl:
    text = path.read_text()
    # Exact source scan supplements, rather than replaces, transitive axiom checks.
    assert not re.search(r'^\s*(?:axiom|opaque|unsafe|partial)\b', text, re.M), path
    assert not re.search(r'\b(?:sorry|admit|native_decide|ofReduceBool|ofReduceNat|trustCompiler)\b', text), path
    assert not re.search(r'^import\s+Challenge\b', text, re.M), path
    imports = re.findall(r'^import (.+)$', text, re.M)
    assert all(x.startswith(('NLA.MI23.', 'Mathlib.', 'LeanCert.')) for x in imports), path

inspection = (OUT / 'inspection.log').read_text()
axioms = re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]", inspection)
assert len(axioms) == 8
assert {name for name, _ in axioms} == set(config['theorem_names'])
assert all(set(x.strip() for x in a.split(',')) == set(config['permitted_axioms']) for _, a in axioms)
assert 'PROJECT_DECLARATIONS_TRAVERSED: 172' in inspection
assert inspection.count('RETAINED_SEMANTIC_DEPENDENCY: ') == 21
assert inspection.count('RETAINED_CERTIFICATE_EDGE: ') == 6
assert 'LeanCert.Validity.verify_strict_upper_bound_dyadic_checked' in inspection
save('review-checks.json', {
    'all_25_proof_freeze_inputs_unchanged': True,
    'changed_from_original_statement_freeze': oldchanges,
    'change_scope': {'README.md': 'Proof status/module map only', 'lakefile.toml': 'defaultTargets only, Challenge to Solution'},
    'both_statement_approvals_and_gate_hashes_match': True,
    'proof_imports_exclude_Challenge_and_other_NLA_projects': True,
    'eight_target_headers_literal_match': True,
    'solution_axiom_reports': 64,
    'additional_independent_export_axiom_reports': len(axioms),
    'unique_project_declarations_traversed': 172,
    'required_retained_semantic_dependencies': 21,
    'required_retained_certificate_consumer_edges': 6,
    'verdict': 'PASS'
})

library_files = {
    'mathlib': ['Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean',
                'Mathlib/Analysis/Matrix/Spectrum.lean', 'Mathlib/Analysis/Matrix/Order.lean',
                'Mathlib/Analysis/CStarAlgebra/Matrix.lean',
                'Mathlib/LinearAlgebra/Matrix/PosDef.lean',
                'Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean'],
    'leancert': ['LeanCert/Tactic/Verification.lean',
                 'LeanCert/Tactic/IntervalAuto/PointIneq.lean',
                 'LeanCert/Validity/DyadicBounds.lean'],
}
libs = {}
for package, files in library_files.items():
    folder = PROJECT / '.lake/packages' / package
    rev = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=folder).decode().strip()
    libs[package] = {'revision': rev, 'files': {rel: {'sha256': sha(folder / rel), 'bytes': (folder / rel).stat().st_size} for rel in files}}
save('inspected-library-sources.json', libs)

terms = r'operatorNorm.*trace|l2_opNorm.*trace|l2_opNorm.*frobenius|charpoly_mul_comm|roots_charpoly_eq_eigenvalues|norm.*eigenvalue'
cmd = ['rg', '-n', terms, '.lake/packages/mathlib/Mathlib/Analysis/Matrix',
       '.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Matrix.lean',
       '.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix']
proc = subprocess.run(cmd, cwd=PROJECT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert proc.returncode == 0
(OUT / 'reuse-search.log').write_bytes(proc.stdout)
save('reuse-search-command.json', {'command': cmd, 'scope': 'Relevant pinned matrix spectral, norm, and positive-definiteness APIs; located facts are reused in the reviewed proof.'})

rubrics = Path('/tmp/nla-lean-formalization/standards/sources/TauCetiProject/TauCetiReview')
standards = Path('/tmp/nla-lean-formalization/standards')
tree_path = standards / 'TauCetiProject_TauCetiReview-tree.json'
commit_path = standards / 'TauCetiProject_TauCetiReview-commit.json'
tree_record = json.loads(tree_path.read_text())
rubric_commit = json.loads(commit_path.read_text())['sha']
assert rubric_commit == 'afb424eda89e8ac96d9eb69f6a88972055a4cd1b'
rubric_names = ['correctness.md', 'scope.md', 'proof-quality.md', 'generality.md', 'reuse.md', 'attribution.md']
tree_blobs = {entry['path']: entry['sha'] for entry in tree_record['tree'] if entry['type'] == 'blob'}
rubric_hashes = {}
for name in rubric_names:
    data = (rubrics / 'rubrics' / name).read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    assert tree_blobs['rubrics/' + name] == blob
    rubric_hashes[name] = {'sha256': sha(rubrics / 'rubrics' / name), 'verified_git_blob_sha1': blob}
save('review-standards.json', {
    'upstream_rubric_repository': 'TauCetiProject/TauCetiReview', 'revision': rubric_commit,
    'inspected_rubrics': rubric_hashes,
    'cached_GitHub_tree_metadata_sha256': sha(tree_path),
    'cached_GitHub_commit_metadata_sha256': sha(commit_path),
    'local_adaptation': {'path': 'docs/lean/REVIEW.md', 'sha256': sha(REPO / 'docs/lean/REVIEW.md')},
    'scope': 'Adapted NLA permanent-target review, not official Tau Ceti endorsement or roadmap admission.'
})
save('scope-integrity.json', {
    'base': freeze['repository_base'],
    'tracked_diff': subprocess.check_output(['git', 'diff', '--name-only'], cwd=REPO).decode(),
    'staged_diff': subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=REPO).decode(),
    'reviewer_writes': ['reviews/proof-referee-1.md', 'reviews/proof-referee-1-evidence/'],
    'all_25_frozen_files_rechecked': True,
    'canonical_sources_unchanged': json.loads((OUT / 'original-sources.json').read_text()),
    'no_math_config_canonical_status_commit_or_push_action': True,
})
print('PASS: eight literal signature matches, 25 frozen inputs unchanged, 64+8 standard-three reports, 172 reachable project declarations, actual checked certificate retained.')
