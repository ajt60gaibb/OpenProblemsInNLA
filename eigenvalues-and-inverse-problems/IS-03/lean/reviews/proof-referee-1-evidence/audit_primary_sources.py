"""Bind independently inspected primary APIs and the adapted ten review angles."""
from pathlib import Path
import hashlib
import json
import subprocess

OUT = Path(__file__).resolve().parent
P = OUT.parents[1]
REPO = P.parents[2]
D = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
sha = lambda b: hashlib.sha256(b).hexdigest()
spec = {
 'mathlib': [
  ('Mathlib/FieldTheory/Separable.lean', 'Exact Bezout definition, map separability and root-set cardinality derived through the nodup root multiset.'),
  ('Mathlib/LinearAlgebra/Eigenspace/Charpoly.lean', 'Actual roots of the characteristic polynomial are eigenvalues over an integral domain.'),
  ('Mathlib/LinearAlgebra/Eigenspace/Basic.lean', 'Nonzero eigenvectors, independence for injective eigenvalues and actual endomorphism powers on eigenvectors.'),
  ('Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean', 'A derived independent family of full cardinality yields an actual basis.'),
  ('Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean', 'Genuine characteristic determinant, reindex/block identities and transport through algebra maps.'),
  ('Mathlib/LinearAlgebra/Trace.lean', 'Basis-independent actual endomorphism trace and its equality to trace of basis matrices.'),
  ('Mathlib/LinearAlgebra/Matrix/Trace.lean', 'Actual diagonal sum and trace transport under additive maps.'),
  ('Mathlib/LinearAlgebra/Matrix/ToLin.lean', 'Actual matrix multiplication/powers correspond to powers of the associated linear map.'),
  ('Mathlib/Data/Matrix/Mul.lean', 'True matrix semiring and generic nonnegative entries of every power, including exponent zero.'),
  ('Mathlib/Algebra/Polynomial/Derivative.lean', 'Actual formal derivative with coefficients, products and powers.'),
  ('Mathlib/RingTheory/Polynomial/Vieta.lean', 'Product coefficients retain a multiset of values with all multiplicities.'),
  ('Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean', 'Genuine symmetric-polynomial Newton identity, all positive degrees.'),
  ('Mathlib/Analysis/Complex/Polynomial/Basic.lean', 'Complex algebraic closedness; no real-spectrum hypothesis.')],
 'leancert': [
  ('LeanCert/Tactic/Verification.lean', 'Explicit kernel mode and actual transitive axiom classification; no fallback to native trust.'),
  ('LeanCert/Tactic/IntervalAuto/PointIneq.lean', 'The actual point expression is certified on the singleton zero interval with exact transport.'),
  ('LeanCert/Validity/DyadicBounds.lean', 'Checked strict upper bound: Boolean domain/enclosure proof entails the actual real inequality.')]
}
records = []
for package, files in spec.items():
    path = D / package
    rev = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    for rel, purpose in files:
        raw = (path / rel).read_bytes()
        original = subprocess.check_output(['git', '-C', str(path), 'show', rev + ':' + rel])
        assert raw == original
        repo = 'leanprover-community/mathlib4' if package == 'mathlib' else 'alerad/leancert'
        records.append({'path': str(path / rel), 'sha256': sha(raw), 'revision': rev,
          'git_blob': subprocess.check_output(['git', '-C', str(path), 'rev-parse', rev + ':' + rel], text=True).strip(),
          'url': f'https://github.com/{repo}/blob/{rev}/{rel}', 'purpose': purpose})
core = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/Lean/Declaration.lean')
records.append({'path': str(core), 'sha256': sha(core.read_bytes()),
    'purpose': 'Actual ConstantInfo value, type, isUnsafe and isPartial APIs used by the independent inspector.',
    'toolchain_commit': '819816b2e0a3bf405af45ae5c7af2491d8f5bee6'})
(OUT / 'primary-api-inputs.json').write_text(json.dumps({'scope': 'Independently read exact proof and inspection APIs; all Git-backed files match immutable package revisions.', 'files': records}, indent=2) + '\n')

rubric = json.loads((P / 'reviews/statement-referee-1-evidence/rubric-inputs.json').read_text())
base = Path('/tmp/nla-lean-formalization/standards/sources/TauCetiProject/TauCetiReview')
for rel, r in rubric['files'].items():
    raw = (base / rel).read_bytes()
    assert sha(raw) == r['sha256']
    assert hashlib.sha1(f'blob {len(raw)}\0'.encode() + raw).hexdigest() == r['git_blob']
assert sha((REPO / 'docs/lean/REVIEW.md').read_bytes()) == rubric['local_adaptation_sha256']
rubric['scope'] = 'Independent final mathematical review of all ten angles as adapted by docs/lean/REVIEW.md. No official Tau Ceti service endorsement or roadmap admission claimed.'
(OUT / 'rubric-inputs.json').write_text(json.dumps(rubric, indent=2) + '\n')
print(json.dumps({'result': 'PASS', 'inspected_primary_API_files': len(records), 'bound_Tau_Ceti_angles': len(rubric['files'])}))
