# IE-10: exact mathematical and numerical specification

Permanent ID: IE-10. Canonical README: eigenvalues-and-inverse-problems/IE-10/README.md. Campaign base: 80c0e3e638b2f26dcb3a00353651fc3d2215dd65. Existing status: Solved. No Lean declaration exists in the canonical problem directory at this base.

## Review and verification boundary

Author: OpenAI Codex AI agent /root/statement_design, 2026-09-28. This is a preimplementation mathematical/model specification. It defines no Lean target and proves no catalog problem. Two independent approvals must bind the final specification before implementation. The complete original page, including resolution, attribution and historical statements, is preserved byte-for-byte as ORIGINAL.md. No canonical file, ID, path or status is changed.

The eventual statement must be a closed safe Target : Prop with concrete definitions, no target axiom, free semantic predicate, assumed algorithm evaluator or placeholder. It must use the shared pinned LeanCert dependency in kernel mode, #assert_statement and #assert_trust kernel. Frozen-boundary Comparator identity and successful elaboration do not prove the mathematical target. A final boundary review must inspect every imported mathematical/model meaning. This symbolic target needs no floating-point experiments or artificial numerical certificate.

## Bound canonical and primary sources

| Raw source | SHA-256 |
| --- | --- |
| eigenvalues-and-inverse-problems/IE-10/README.md | 61c9f5e820b4201e6b34e55cd43e3b65bc0e746dcdef6551ccfe50602ebe644a |
| eigenvalues-and-inverse-problems/IE-10/problem.tex | 2c805f2f4f15f102b021a34292ccf479caaab5a234e1070a1bb5ecd6c5c3d51c |
| references/colbrook-round3-2026-09-11/manuscripts/IE-10.tex | 5de33745924855b831a011e39d4fa66e534b5ab9cb82c21756fda04e41925a23 |

## Exact target and quantifier order

There exist two real constants C>0 and c>0, chosen once, such that for every natural n>=3 and every natural k with 2<=k<n, the probability that the eigenvector condition number of the complex cyclic-shift Krylov compression is at most C*(n:Real)^c is at least 99/100. The exponent is the ordinary positive-base real power, not a natural exponent silently fixed to the resolution's value. The probability threshold and matrix inequality are non-strict. C and c precede n and k and do not depend on any draw.

The original target is the existence of these constants. The resolution's values C=1700,c=3 and its stronger expectation bound 17*n^2*k explain the solved status but are not additional required conjuncts. In particular, the expectation estimate and the simultaneous-in-k corollary must not replace this per-(n,k) probability statement.

## Concrete cyclic matrix, random law and orthonormal compression

Use zero-based indices Fin n. The matrix C_n has entry 1 at (i,j) exactly when i=(j+1) mod n and entry 0 otherwise. Thus it moves basis column e_j to e_(j+1 mod n), including the wraparound. Only n>=3 occurs in the target; any helper convention at n=0 is outside it.

Take the concrete finite product of 2n copies of the real standard Gaussian probability measure N(0,1), indexed by Fin n times Fin 2. For a draw omega let g_j=omega_(j,0)+I*omega_(j,1). Put b=g/||g||_2 if ||g||_2>0, and b=e_0 if g=0. Both real components have variance 1. The common scale sqrt(2) relative to the variance-one standard complex Gaussian cancels under normalization, so this gives exactly the uniform complex unit-sphere law. The density depends only on the Euclidean radius and is unitary invariant; g=0 has measure zero. No real-sphere start, random matrix, Haar subspace or separately randomized basis is used.

The vector norm is sqrt(sum_j |v_j|^2). Inner products are sum_j conj(u_j)*v_j. Set w_j=C_n^j b for j=0,...,k-1. Define canonical Gram–Schmidt in that order:
- u_j = w_j - sum_(ell<j) q_ell * inner(q_ell,w_j);
- q_j=u_j/||u_j||_2 when ||u_j||_2>0, and q_j=0 otherwise.

The full-rank event is that every one of these k residual norms is positive. On this event q_0,...,q_(k-1) are orthonormal and span precisely the original Krylov space. Let Q have these vectors as its columns and set H=Q* C_n Q, where the star is conjugate transpose, giving a complex k-by-k matrix. These definitions are finite recursions, sums, products and square roots; no oracle chooses a favorable basis.

On the complementary rank-failure event, define the compression condition number below to be infinity. This prevents empty-basis predicates from making failure count as success. This is the same probability target: for this cyclic shift the full-rank event has probability one. Indeed the unitary Fourier eigenbasis has n distinct eigenvalues; all transformed starting coordinates are nonzero almost surely, so the first k Krylov columns are a diagonally rescaled rectangular Vandermonde system of rank k. This is a correspondence justification, not a new premise imposed on draws. It must not be used to discard a positive-probability failure event in another model.

Any orthonormal basis of the same full-rank Krylov space differs by a unitary k-by-k change of basis. The compressed matrices are unitarily similar, and the spectral norms of diagonalizers and their inverses, hence their infimum, are invariant. Thus this deterministic basis selection preserves the original basis-independent statement.

## Exact extended condition number

For each complex k-by-k H, let S(H) be the set of nonnegative extended-real numbers
ofReal(||V||_2 * ||V^(-1)||_2)
over every complex k-by-k V with det(V)!=0 and every d:Fin k->Complex such that
H=V * diagonal(d) * V^(-1).
The matrix norms are the actual operator norms induced by complex Euclidean vector norms, e.g. the continuous-linear-map norm of Matrix.toEuclideanLin. They are not entrywise supremum norms or Frobenius norms. The explicit determinant condition makes the total matrix inverse its genuine inverse.

Define kappa(H)=sInf S(H) in the complete lattice of nonnegative extended reals. The empty infimum is infinity, so every nondiagonalizable H has precisely the stipulated value. Arbitrary repeated eigenvalues and all diagonalizers, column scalings and column reorderings are included. There is no simple-spectrum restriction.

The random quantity K(omega) is kappa(H(omega)) on the full-rank event and infinity otherwise. The success event is K(omega)<=ofReal(C*(n:Real)^c); its measure under the concrete finite product Gaussian law must be >=ofReal(99/100).

Do not replace the infimum comparison by existence of a diagonalizer attaining the threshold. An equivalent finite-threshold event can instead say: the Krylov residuals are positive and for every real delta>0 there exist V,d as above with
||V||_2*||V^(-1)||_2 < C*(n:Real)^c+delta.
This correctly retains a possibly unattained infimum and the closed threshold. It also forces a diagonalizer to exist; a nondiagonalizable H fails. A Lean implementation may use either this exact event or the extended infimum, provided the final review checks this equivalence.

All maps in the Gram–Schmidt construction are piecewise semialgebraic on real and imaginary coordinates. At any finite threshold the diagonalization/norm constraints and the delta characterization are expressible by finitely many real polynomial relations and quantifiers (operator-norm bounds can be expressed by quadratic-form inequalities). Real quantifier elimination therefore makes the condition-number sublevel sets Borel measurable. Alternatively, a later implementation may establish measurability directly. A raw nonmeasurable choice of eigenbasis is unnecessary.

## Complete endpoints and implementation obligations

Retain every n>=3, k=2, k=n-1, the exceptional deterministic starts, rank failure, zero Gaussian draw, repeated eigenvalues, defective compressions, both universal constants and the exact 99/100 bound. The same random start could be used to couple different k, but the target does not require simultaneous success over k. Only the start is random.

The complete canonical README and the bound manuscript Section 1 were read for the exact target. Its Section 2 explicitly derives the normalized Gaussian sphere representation and the almost-sure Krylov dimension. Theorem 1 supplies the stronger expectation estimate; no part of the weighted-polynomial proof is a required substitute for the original matrix model.

Before code, two independent reviews must check the finite Gaussian law, conjugation convention, cyclic orientation, Gram–Schmidt failure handling, actual operator norm, extended empty-infimum convention and finite-threshold equivalence. Formalizing these concrete helper definitions is enough to state the target; proving unitary invariance, full rank, measurability, the expectation estimate or the final probability bound are later proof/correspondence obligations, not algorithm or target axioms.
