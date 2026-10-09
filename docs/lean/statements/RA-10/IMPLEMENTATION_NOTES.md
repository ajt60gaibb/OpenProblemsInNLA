# RA-10 implementation correspondence

Author: OpenAI Codex AI agent /root/statement_design, 2026-09-28.
The preimplementation mathematical specification and canonical README are unchanged.
This records the concrete API choices for the independent Lean-boundary reviewers.

The live source is lean-statements/NLA/Statements/RA10.lean. The separately named
Reviewed/RA10.lean snapshot is created only after the live definition compiled.
No proof of Target is supplied.

## Nuclear norm

NuclearNorm uses the pinned Mathlib LinearMap.singularValues on
Matrix.toEuclideanLin M. The latter is Matrix.toLpLin 2 2, taking ordinary
matrix-vector multiplication between real Euclidean spaces, not the sup-norm
space of unbundled coordinate functions.

The singular-value API defines nonnegative square roots of the eigenvalues of
the Euclidean adjoint composed with the map, counted with multiplicity and
ordered decreasingly. For the matrix map, this is the spectrum of the usual
real transpose product. The API is indexed by all natural numbers and zero
after the dimension of the domain. Summing at i.val for i : Fin n therefore
includes exactly all n singular values, including zero values, and is the
canonical nuclear norm for every real square matrix. No surrogate norm, assumed
spectral oracle, or restriction to symmetric differences is used.

Pinned API sources at 0df444a360eaa60ab8c11dca51a86af692955474:

- Mathlib/Analysis/InnerProductSpace/SingularValues.lean:
  LinearMap.singularValues, singularValues_fin,
  singularValues_of_finrank_le, singularValues_nonneg.
- Mathlib/Analysis/InnerProductSpace/PiL2.lean:
  Matrix.toEuclideanLin, an abbreviation for Matrix.toLpLin 2 2.
- Mathlib/Analysis/Normed/Lp/Matrix.lean:
  Matrix.toLpLin_apply, ordinary multiplication in WithLp 2 coordinates.

## Spectral data and function domain

OrderedPSDSpectralDecomposition records nonnegative antitone eigenvalues,
orthonormal columns of the square real matrix Q, and exact equality with
SpectralMatrix, whose entries are the full sum of eigenvalue times two column
coordinates. These conditions are precisely a PSD ordered orthonormal
eigendecomposition. Orthonormal square columns form a complete orthonormal
basis; reconstruction gives symmetry and a nonnegative quadratic form.
Conversely the real symmetric spectral theorem supplies such data for every
PSD matrix. Universal quantification over the data preserves all allowed
choices within repeated eigenspaces and at zero eigenvalues.

FunctionMatrix uses that full spectral sum with f applied to each eigenvalue.
This is independent of the choice of orthonormal basis within each eigenspace:
on an eigenspace with repeated value a, the contribution is f(a) times its
orthogonal projector. FunctionTruncation deliberately retains the selected
first k columns via the zero-based condition index.val < k. Both truncations
of a given matrix use exactly the same eigenvalues and Q.

OperatorMonotoneOnNonnegative quantifies over every positive dimension and
every pair of those PSD spectral decompositions. It assumes the concrete PSD
condition for H-G and concludes the same for f(H)-f(G). This is exactly the
all-size real operator-monotone condition; the size-zero condition, if
included, would be tautological. It is neither scalar monotonicity nor a
single-dimension approximation.

AdmissibleFunction requires continuity and nonnegativity only on the closed
nonnegative half-line. Values on negative inputs are unrestricted and unused.
A function originally defined on [0,infinity) may be extended arbitrarily to
negative arguments; this introduces no condition on that extension.

## Original target and boundary cases

Target chooses a real C >= 1 before TransferBound quantifies dimensions,
matrices, both selected spectral decompositions, epsilon and f. The premise
uses identity-function truncation, exactly A_k and Ahat_k. The conclusion
uses function truncation on the same respective bases, including when f(0)>0
or the selected truncation has rank less than k. No commutation, ordering,
strict eigenvalue gap, invertibility, positive-tail or epsilon>0 condition
appears.

Only the original existential constant proposition is registered. The
archived proof's stronger witness C=11 is not imposed on this statement.

## Development evidence

The live module compiled using the pinned Lean 4.33.1 macOS executable and
pinned Mathlib/LeanCert caches. The local receipt is
/private/tmp/nla-ra10-evidence/result.json and its output is RA10.log in that
directory. The statement and LeanCert trust assertions passed; the axiom
report is exactly propext, Classical.choice and Quot.sound.

This development check is not an authoritative Linux sandboxed Comparator run
and does not prove the mathematical proposition. Independent boundary reviews
and project-level reproduction remain separate gates.
