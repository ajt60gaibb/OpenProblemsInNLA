# Independent preimplementation review: truncated inverse

Reviewer and implementation author: `/root/independent_math_review`, reviewing
coordinator `/root`'s proposed mathematical contract before writing Lean code.
The coordinator will independently review the implementation.

Approved. For an n-by-n real matrix M, define

sigmaInvSum(M,r) = sum over i in Fin(n−r) of (singularValue M i)⁻¹ squared.

This equals the proposed integer power −2, uses the actual descending
zero-based forward singular values, and is zero when r≥n. Real inverse is
totalized at zero; no positivity is inferred from this definition alone.

For det(M)≠0 and r<n, construct V,H : Matrix (Fin n) (Fin r) ℝ and
Z : Matrix (Fin n) (Fin n) ℝ with

- VᴴV=I;
- H=M⁻¹V;
- M⁻¹=Z+HVᴴ;
- frobeniusNorm(Z)²=sigmaInvSum(M,r);
- opNorm(Z)²≤sigmaInvSum(M,r).

V must contain the last r **left** singular vectors of M, since these form
the input basis of M⁻¹. With Z=M⁻¹(I−VVᴴ), the image on the retained left
singular vector is the reciprocal singular value times its corresponding
right singular vector, and the image on removed left directions is zero.
The true orthonormal-basis Frobenius identity proves the exact squared sum.
The already proved opNorm≤frobeniusNorm gives the operator-square bound.
The case r=0 is included; n=0 cannot satisfy r<n. No measurable choice of
random singular vectors is asserted or required by this deterministic result.

For arbitrary (possibly singular) M, the source one-based condition
sigma_(n−r)(M)≥mu>0 means exactly
mu≤singularValue M (n−r−1), with r<n. Antitonicity then proves
mu≤singularValue M i and hence positivity for every i in Fin(n−r).
The additional source guard 1≤r may be retained by applications but is not
needed for this deterministic implication. Thus the eventual A5 theorem
must not silently require full nonsingularity merely to use retained terms.

All singular-vector identities and Frobenius-basis identities will be proved
from the actual SVD infrastructure. No source bound, inverse-SVD identity,
measurability assertion, or probabilistic premise will be introduced as an
axiom. Profile-weighted sum estimates remain a separate later dependency.

The coordinator subsequently approved this stronger exact singular-matrix
interface before implementation: if mu>0, r<n and
mu≤singularValue M (n−r−1), construct R,U with UᴴU=I,
MR=I−UUᴴ, RU=0, frobeniusNorm(R)²=sigmaInvSum(M,r), and
opNorm(R)≤mu⁻¹. The retained positive left vectors extend to a complete
orthonormal basis; zero raw left singular vectors are never called unit
vectors. The nonsingular inverse decomposition follows by multiplication by
M⁻¹. This interface is shared with the independently reviewed A5 proof.

Implementation completed and compiled: NLA/IE06/TruncatedInverse.lean,
SHA-256 `2ae98396774c1447173220cad93ca006c1e3247a333171401c2acd0004bbbe92`.
All 33 local declarations have individual LeanCert kernel-policy assertions
and axiom output restricted to propext, Classical.choice, and Quot.sound.
The pinned-runtime local-cache log and receipt are in reviews/truncated-inverse/;
this does not claim a fresh dependency rebuild or replay of cached dependencies.
The actual singular-M result is `exists_retained_decomposition`; the actual
nonsingular result is `exists_inverse_decomposition`. The latter's discarded
orthonormal columns span the last r left singular directions; an arbitrary
orthonormal completion of the retained positive left vectors is sufficient
and is the concrete construction used. This is equivalent to choosing their
individual SVD vectors for the stated decomposition, without asserting equality
of these two choices. The coordinator will independently review the frozen code.
