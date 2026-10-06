# Gaussian regression inverse-moment specification

The root reviewer independently approved this exact contract before code on
2026-10-06. The author owns GaussianRegression.lean; prior radial and Frobenius
modules remain frozen and reviewed.

Let m≥1 and n≥m+2q, with natural m,n,q. For a deterministic Euclidean vector
v in R^m and literal G~GaussianNull.gaussianRect m n, set W=G*Gᵀ and
Q_v(G)=vᵀW⁻¹v. The inverse here is Mathlib's ordinary inverse (zero at singular
matrices). Prove full row rank almost everywhere, measurable/integrable Q_v^q,
and the exact integral

`∫ Q_v(G)^q = ‖v‖^(2q) / ∏j∈range q (n-m+1-2(j+1))`.

The dimension in the denominator is computed as natural n-m+1 and then cast
to real. Every factor is positive. Zeroth moments and v=0 use Lean's standard
0^0=1 convention. This identity is not a claimed pseudoinverse theorem on the
singular exceptional set.

For fixed remaining rows B of full row rank, prove the deterministic Schur
identity: the first diagonal entry of W⁻¹ equals the reciprocal squared length
of the first row projected onto the orthogonal complement of rowSpan(B),
whenever the full row matrix is nonsingular in its Gram matrix. The complement
has dimension n-m+1. Integrate the first row using a deterministic orthonormal
basis selected separately for each fixed B and the proved radial inverse
moment. Fubini uses a measurable inverse-matrix integrand; no globally
measurable random basis selector is assumed. Fixed-v orthogonal invariance of
the entire Gaussian matrix law yields the general direction.

The actual Moore–Penrose inverse, its operator norm identity, the Gaussian
probe moment comparison, and the A2 tail theorem remain separate later steps.
No manuscript theorem, custom axiom, or unproved regression assertion may be
used as a premise of a claimed unconditional result.
