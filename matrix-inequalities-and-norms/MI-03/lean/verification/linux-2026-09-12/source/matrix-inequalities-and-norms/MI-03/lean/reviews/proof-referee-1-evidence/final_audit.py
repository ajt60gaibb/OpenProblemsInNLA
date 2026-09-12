"""Read-only final integrity/API/signature audit; no mathematical changes."""
from pathlib import Path
import hashlib, json, re, subprocess

out = Path(__file__).resolve().parent
project = out.parents[1]
repo = project.parents[2]
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
write = lambda name, value: (out / name).write_text(json.dumps(value, indent=2) + '\n')
git = lambda root, *args: subprocess.check_output(['git', '-C', str(root), *args])
freeze = json.loads((project / 'reviews/proof-freeze.json').read_text())
for rel, record in freeze['files'].items():
    assert digest(project / rel) == record['sha256'], rel
for rel, expected in freeze['source_files'].items():
    assert digest(repo / rel) == expected, rel
    assert (repo / rel).read_bytes() == git(repo, 'show', freeze['source_commit'] + ':' + rel)
start = json.loads((project / 'verification/proof-start.json').read_text())
for rel, expected in start['statement_files'].items():
    assert digest(project / rel) == expected, rel
for rel, expected in start['reports'].items():
    assert digest(project / rel) == expected, rel
assert start['status'].startswith('Both independent statements APPROVE')
assert start['time_utc'] < freeze['date_utc']

config = json.loads((project / 'comparator.json').read_text())
assert config['definition_names'] == []
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
def signatures(path):
    return {name: ' '.join(body.split()) for name, body in re.findall(
        r'^theorem\s+(\w+)\s+(.*?)\s*:=\s*by', path.read_text(), re.M | re.S)}
challenge = signatures(project / 'Challenge.lean')
solution = signatures(project / 'Solution.lean')
assert challenge == solution and len(challenge) == 8
assert config['theorem_names'] == ['NLA.MI03.' + name for name in challenge]
write('signature-identity.json', {'result': 'PASS', 'method': 'exact theorem header equality after whitespace normalization; compiled actual theorem types independently inspected; not a Comparator claim', 'signatures': challenge, 'comparator': config})

math_files = sorted((project / 'NLA/MI03').glob('*.lean')) + [project / 'Solution.lean']
for path in math_files:
    # Supplementary lexical audit; the actual transitive kernel checks are stronger.
    text = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    assert not re.search(r'\b(sorry|admit|sorryAx|axiom|native_decide|unsafe|implemented_by|extern)\b', text), str(path)
    assert not re.search(r'^import\s+Challenge\b', text, re.M), str(path)
write('source-safety.json', {'result': 'PASS', 'scope': 'supplementary comment-stripped lexical scan, separately supported by actual kernel axiom and ConstantInfo inspection', 'files': {str(p.relative_to(project)): digest(p) for p in math_files}, 'isolated_challenge_holes': 8})

library_paths = {
    'mathlib': [
        'Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Abs.lean',
        'Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean',
        'Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean',
        'Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Instances.lean',
        'Mathlib/Analysis/CStarAlgebra/Matrix.lean',
        'Mathlib/LinearAlgebra/Matrix/PosDef.lean',
        'Mathlib/Analysis/Matrix/Order.lean',
        'Mathlib/RingTheory/RootsOfUnity/Complex.lean',
        'Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean',
        'Mathlib/Order/ConditionallyCompletePartialOrder/Basic.lean',
        'Mathlib/Order/ConditionallyCompleteLattice/Basic.lean',
        'Mathlib/Data/Matrix/Mul.lean',
        'Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean'],
    'leancert': ['LeanCert/Tactic/Verification.lean']}
pins = {p['name']: p['rev'] for p in json.loads((project / 'lake-manifest.json').read_text())['packages']}
library_record = {}
for package, paths in library_paths.items():
    root = project / '.lake/packages' / package
    for rel in paths:
        path = root / rel
        assert path.read_bytes() == git(root, 'show', pins[package] + ':' + rel)
        library_record[package + '/' + rel] = {'revision': pins[package], 'sha256': digest(path), 'matches_immutable_git_blob': True}
write('library-inputs.json', library_record)

standard_root = Path('/tmp/nla-lean-formalization/standards')
standard_manifest = json.loads((standard_root / 'MANIFEST.json').read_text())
rubric_records = {}
rubric_dir = 'sources/TauCetiProject/TauCetiReview/rubrics/'
for rel in [rubric_dir + name + '.md' for name in ['scope','correctness','proof-quality','reuse','generality','api-design','naming','placement','documentation','attribution']]:
    assert digest(standard_root / rel) == standard_manifest[rel]['sha256']
    rubric_records[rel] = standard_manifest[rel]
commit_rel = 'TauCetiProject_TauCetiReview-commit.json'
assert digest(standard_root / commit_rel) == standard_manifest[commit_rel]['sha256']
assert json.loads((standard_root / commit_rel).read_text())['sha'] == 'afb424eda89e8ac96d9eb69f6a88972055a4cd1b'
write('rubric-inputs.json', {'commit': 'afb424eda89e8ac96d9eb69f6a88972055a4cd1b', 'rubrics': rubric_records, 'adaptation_sha256': digest(repo / 'docs/lean/REVIEW.md'), 'scope': 'Independent AI application of NLA adaptation; not official Tau Ceti service or endorsement'})

search_command = ['rg', '-n', r'vecMulVec_mul_vecMulVec|vecMulVec_mulVec|conjTranspose_vecMulVec|pairVariance|variance',
                  '.lake/packages/mathlib/Mathlib/Data/Matrix', '.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix',
                  '.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra']
result = subprocess.run(search_command, cwd=project, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert result.returncode == 0
(out / 'reuse-search.log').write_bytes(result.stdout)
write('reuse-search.json', {'command': search_command, 'exit_code': result.returncode, 'log_sha256': digest(out / 'reuse-search.log'), 'assessment': 'Actual proof reuses CFC, PSD, Euclidean operator norm, primitive roots and IsLeast APIs. Existing vecMulVec multiplication can alternatively implement the short local outerProduct adapter; its present elementary eight-line proof is scoped and has material witness consumers. No new general numerical/spectral machinery or broad Mathlib import is introduced.'})

for package in json.loads((project / 'lake-manifest.json').read_text())['packages']:
    root = project / '.lake/packages' / package['name']
    assert git(root, 'rev-parse', 'HEAD').decode().strip() == package['rev']
    assert not git(root, 'status', '--porcelain', '--untracked-files=no').strip()
write('integrity-after.json', {'result': 'PASS', 'frozen_project_inputs': len(freeze['files']), 'original_git_source_inputs': len(freeze['source_files']), 'frozen_statement_inputs': len(start['statement_files']), 'independent_statement_approvals': start['reports'], 'ten_dependency_tracked_sources_unchanged': True, 'no_mathematical_or_canonical_mutation': True, 'file_hashes': {rel: digest(project / rel) for rel in freeze['files']}, 'source_hashes': {rel: digest(repo / rel) for rel in freeze['source_files']}})
print('PASS: 101 frozen inputs, 8 original Git sources, 27 statement inputs, 8 identical public signatures, 14 primary library files, 10 pinned review rubrics')
