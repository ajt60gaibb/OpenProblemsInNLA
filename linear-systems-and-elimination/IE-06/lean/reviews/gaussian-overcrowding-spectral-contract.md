# Deterministic spectral-to-principal-minor implication for A3

Proposed by `/root/independent_math_review` for coordinator approval before
implementation. This is the deterministic dependency of the already reviewed
Gaussian overcrowding moment proof. Gaussian principal-minor moments remain
owned by `/root/infrastructure`.

The core theorem uses R : Matrix (Fin m) (Fin n) ℝ, natural m,n,r satisfying
1≤r≤m≤n, t:ℝ with t>0, and (R*Rᴴ).PosDef. With H=(R*Rᴴ)⁻¹, prove

singularValue R (m−r) ≤ t →
∃ S : Finset (Fin m), S.card=r ∧
  (t^(2*r))⁻¹ / (m.choose r : ℝ) ≤
    Matrix.det (H.submatrix (Subtype.val : S→Fin m) Subtype.val).

This is the original one-based singular index m−r+1, with positive threshold
and all index guards explicit. The principal subset uses exactly the subtype
determinant representation used by GaussianPrincipalMoments. Since r≤m,
the binomial denominator is positive. No probability or spectral premise
besides the stated event and positive-definite Gram matrix is added.

Supporting interfaces:

1. Forward norm domination on equal Euclidean input spaces implies domination
   of every valid singular index. Consequently extracting any injectively
   selected rows cannot increase the corresponding singular values.
2. The sum of r-by-r principal minors of a positive-semidefinite Hermitian
   matrix is the sum of all r-fold products of its actual spectral eigenvalues.
   This will be derived from the proved Mathlib characteristic-polynomial
   principal-minor formula and the true spectral diagonalization, with no
   unproved elementary-symmetric identity assumption.
3. A lower quadratic-form bound on an at-least-r-dimensional subspace gives
   the corresponding sorted eigenvalue lower bound by the same trailing-space
   dimension-intersection argument already used for A6.

Proof route avoiding a separate rectangular adjoint singular-value identity:
Take the forward trailing Gram subspace of R at index m−r. Its orthogonal
complement has dimension m−r. The orthogonal complement W of that space's
image under R therefore has dimension at least r. The already proved adjoint
upper-bound argument gives ||Rᴴx||≤t||x|| on W. Cauchy–Schwarz applied to
Rᴴx and RᴴHx, with RH identities discharged by positive definiteness, yields
xᵀHx≥t⁻²||x||². Min–max gives at least r eigenvalues of H at least t⁻².
All eigenvalues are nonnegative, so one term in the spectral elementary
symmetric sum is at least t^(−2r). The principal-minor identity and averaging
over exactly choose(m,r) subsets produce the displayed witness.

The final square-matrix wrapper retains first m=n−2q rows of G, with j<n,
q≥1, r=j+1−2q≥1. The arithmetic identity m−r=n−j−1 aligns the one-based
source event sigma_(n−j)(G)≤t with the core theorem through row deletion.
The almost-sure Gram positivity and moment integrability are supplied by
separately proved Gaussian theorems during assembly, never assumed as a
new stochastic axiom. No additional failure probability is introduced.

Coordinator `/root` approved this complete contract before implementation,
including the inverse-Gram Cauchy proof route, subtype principal minor, and
square row-deletion index arithmetic. The independent Gaussian principal
moment/tail implementation uses the identical finite-subset determinant.
