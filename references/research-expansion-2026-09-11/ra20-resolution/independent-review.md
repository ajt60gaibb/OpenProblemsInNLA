# Independent review: RA-20 is refuted at n=s=3

Reviewed original target: `/private/tmp/nla-pr111/randomized-and-low-rank-approximation/RA-20/README.md`, as introduced by PR 111 head `450ee69e20e54bb687240e01477cf95b0de61e0e`.

**Verdict: PASS.** The exact target's generic smooth-locus critical-point count is **e_(3,3)=3**, whereas its displayed s=3 formula gives **4**. This derivation is independent and uses no external claimed ED-degree result.

## Direct computation of the variety and its smooth locus

Every symmetric hollow 3-by-3 matrix has the unique form

\[
 X(a,b,c)=\begin{pmatrix}0&a&b\\a&0&c\\b&c&0\end{pmatrix}.
\]

Direct determinant expansion gives det X=2abc. For a 3-by-3 matrix, rank at most two is equivalent to determinant zero. Thus the specified variety W_(3,3), in its linear ambient hollow symmetric space, is exactly the reduced hypersurface

\[
 V(abc)=V(a)\cup V(b)\cup V(c)\subset\mathbb C^3.
\]

Its defining polynomial is square-free. Its gradient is (bc,ac,ab), or twice this vector if one uses det X. Therefore its smooth locus consists exactly of points with **one zero coordinate and two nonzero coordinates**. Points with at least two zero coordinates are singular. The three coordinate planes are irreducible components, and at a point on just one plane the tangent space is that plane's tangent space.

This smoothness statement concerns the variety W_(3,3), as required by the target. Nonzero coordinate-axis matrices actually have matrix rank two; they are nevertheless singular points of this reducible constrained variety. Counting the entire rank-two stratum would not implement the target's smooth-locus convention.

## All generic critical points, with no missing complex points

Write p=u12, q=u13, r=u23 for the three off-diagonal entries of symmetric data U. On this hollow space the exact full-Frobenius distance is

\[
 d_U(a,b,c)=u_{11}^2+u_{22}^2+u_{33}^2
       +2[(a-p)^2+(b-q)^2+(c-r)^2].
\]

There is no complex conjugation. Its differential in coordinate directions has coefficients 4(a-p), 4(b-q), 4(c-r).

On the smooth part of V(a), the tangent directions are arbitrary changes in b and c. Criticality is therefore exactly b=q and c=r, so its only candidate is (0,q,r). Likewise, the other two components give (p,0,r) and (p,q,0).

The condition pqr != 0 is a nonempty Zariski-open condition on the whole space of symmetric data U. For every U in this open set, all three candidates have exactly one zero coordinate, hence lie in the smooth locus; they are distinct. Every smooth point belongs to exactly one component, and the component equations above exhaust its tangent criticality conditions. Thus there are exactly three complex critical points. Their restricted Hessians are each 4 I_2, with determinant 16, so all are nondegenerate and have multiplicity one. The generic count is consequently 3 whether ordinary distinct-point counting or generic algebraic multiplicity is used.

No critical points at singular intersections are included: the target explicitly counts only on the smooth locus. This exclusion is part of the definition, not an arbitrary restriction. All data diagonal entries add only a constant, so no assumption about their values or reality is used in the generic derivation.

## Exact rational witness

Take

\[
 U=\begin{pmatrix}1&1&2\\1&2&3\\2&3&3\end{pmatrix},
 \qquad(p,q,r)=(1,2,3).
\]

This belongs to the explicit generic open set pqr != 0. Its three critical coordinate triples are

\[
 (0,2,3),\qquad(1,0,3),\qquad(1,2,0).
\]

The determinant-gradient vectors are respectively (12,0,0), (0,6,0), and (0,0,4), so all three are smooth. The distance-gradient vectors are respectively (-4,0,0), (0,-8,0), and (0,0,-12), perpendicular in the bilinear coordinate metric to the corresponding tangent planes. Their full-Frobenius squared distances are 16, 22, and 32. Each has a nonzero 2-by-2 principal minor and determinant zero, so has rank exactly two.

Independent exact standard-library Fraction verification is saved as `verify_counterexample.py`, with results in `exact-results.json`. It checks the determinant coefficient expansion, each matrix's rank, smoothness gradient, tangent criticality, restricted Hessian determinant, and full-Frobenius distances. All checks pass. The symbolic generic argument above, rather than a single example, establishes the ED count.

## Resolution disposition

The original canonical target explicitly groups all four formulas as one conjectural target for every stated n and s. The allowed case n=s=3 violates that conjunction: 27(3-3)+4=4 != 3. Accordingly **Solved — refuted / negative resolution** is logically justified for this exact original target, with the original formulas and parameter range retained verbatim.

The resolution must state its precise scope: it refutes the displayed joint conjecture at n=s=3 and establishes e_(3,3)=3. It does **not** claim proofs or refutations of the s=1, s=2, or s=4 formulas, does not establish a corrected all-n formula for s=3, and does not settle the s=3 formula for n>=4. These unclaimed individual formulas need not convert the single refuted conjecture into a partial resolution. Conversely, silently excluding n=3 from the s=3 formula or replacing the target with a corrected sequence would alter the registered mathematical target and should not be done.

The source-attribution and table-consistency questions are separate editorial checks; this report establishes the stated canonical target's failure directly and does not claim any external author's intended convention has been reconstructed.
