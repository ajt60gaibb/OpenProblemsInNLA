# RA-19 exact mathematical and numerical specification

Author: OpenAI Codex AI agent `/root`, 2026-09-28. Preimplementation specification; two independent approvals precede Lean implementation. Permanent ID RA-19, canonical path `randomized-and-low-rank-approximation/RA-19/README.md`, campaign base `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. Complete original is preserved in ORIGINAL.md, including credits and historical evidence. No canonical changes or mathematical proof are made.

## Original target and concrete geometry

For every n>=3, generic complex n-by-n data U have exactly 5*n-7 critical points of the complex **bilinear** squared distance on the smooth locus of V={X:det X=0, X_00=0}. Count distinct points of the generic finite critical set, not critical points over the reals, conjugate/Hermitian distance, singular-locus points, or just solutions of an unrelated resultant. Dimension n=2 is explicitly excluded by the original source correction.

Use square matrices indexed by Fin n and the actual polynomial determinant and adjugate. For uniform helper definitions avoiding a Fin 0 coordinate, one may quantify a natural d>=0 and set n=d+3. This is exactly the domain of every integer n>=3, without a finite cutoff. The formula then remains 5*(d+3)-7, equal to 5*d+8; there is no problematic natural subtraction.

Define the determinant differential on a direction Z by

`DetDifferential(X,Z) = trace(adjugate(X) * Z) = sum_i sum_j adjugate(X)_ij * Z_ji`.

This is the standard first derivative of det(X+tZ) at t=0 even for singular X, not det(X)*trace(X^(-1)Z), which would fail on the target variety. Matrix multiplication and trace are ordinary complex bilinear operations, with no conjugation.

Define `SmoothPoint(X)` by X_00=0, det X=0, and existence of a matrix Z with Z_00=0 and DetDifferential(X,Z)!=0. This is precisely the smooth locus of the determinant hypersurface restricted to the fixed-zero hyperplane. The restricted determinant is nonzero (the permutation swapping coordinates 0,1 and fixing all others gives a surviving monomial) and squarefree: it has degree at most one in every individual remaining entry, so no nonconstant irreducible factor can occur twice. The Jacobian criterion for this reduced complex hypersurface therefore gives exactly the displayed nonvanishing restricted derivative criterion. In particular, all rank<=n-2 points are excluded, and any rank n-1 point whose determinant gradient lies in the X_00 normal direction is also excluded. Merely requiring rank n-1 is insufficient.

For a smooth point, its tangent directions are exactly all Z with Z_00=0 and DetDifferential(X,Z)=0. Define a critical point for data U to be SmoothPoint(X) and

`forall Z, Z_00=0 -> DetDifferential(X,Z)=0 -> sum_i sum_j (X_ij-U_ij)*Z_ij=0`.

The omitted common factor 2 is nonzero in Complex, so this is precisely the derivative of sum_ij(X_ij-U_ij)^2 vanishing on the tangent space. The same coordinate pair occurs in the displacement and direction, without swapping or conjugating. No Lagrange-multiplier witness whose projection could lose points is used.

## Genericity and exact finite count

Use an actual `MvPolynomial (Fin n × Fin n) Complex` p in all data entries U, with an explicit matrix U0 such that evaluation p(U0)!=0. Require the exact count for every U with p(U)!=0. This is a nonempty principal Zariski-open set of the entire data space. It is equivalent to the source's generic condition outside some proper algebraic exceptional set: every nonempty affine Zariski-open contains a nonempty principal open. No normal form, genericity oracle, sampled set, diagonal-block condition or independent random distribution is substituted.

Represent exactly 5*n-7 critical points by `Nonempty ({X // Critical(U,X)} ≃ Fin (5*n-7))`, or explicitly finite-set cardinality with exactly the same semantics. A bijection certifies both finiteness and complete distinct-point count, and avoids any totalized cardinality of an infinite set. It includes all smooth critical points; no ordering, multiplicity weight, nonisotropic assumption or nonzero Lagrange parameter is imposed unless shown to follow generically as later proof data.

The Target quantifier order is all d (n=d+3), then one polynomial p and a nonvanishing witness U0, then all U in its nonvanishing locus, then existence of the finite critical-set bijection. It is a concrete closed proposition with polynomial, matrix, finite-sum and type-equivalence meanings.

## Source correspondence and scope

The canonical README and the retained Stepaniants solution, especially Section 3 Lemma 2, were read. The latter explicitly supplies the reduced-hypersurface/Jacobian justification above and distinguishes singular-locus or gradient-degenerate points. This is a mathematical correspondence explanation for the statement, not a new target assumption or proof of the conjecture. The spectral-curve resultant and its degree are resolution techniques and must not replace this original smooth critical-point count.

Keep the original author's resolution and Kubjas–Sodomaco–Tsigaridas conjecture credit. Final review must inspect actual Matrix.adjugate/trace meanings and both uses of entry indices, genericity and exact cardinality. Closed Target uses pinned LeanCert kernel trust and shared #assert_statement/#assert_trust kernel; frozen Comparator identity validates correspondence, not the ED-degree theorem. No polynomial elimination or numerical root computation is needed merely to state this exact all-dimensional target.
