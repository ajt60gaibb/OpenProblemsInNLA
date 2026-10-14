# RA-10 frozen nuclear-norm homogeneity: independent final review

**Accepted for aggregate import.** I independently reviewed
`NLA/Proofs/RA10/NuclearNormHomogeneity.lean` at SHA-256
`f3b7c30c5d04e63bf92596aef9f418a0f9a5b6a015439136e7823d35c4c23eca`
against the already independently approved
`NUCLEAR_IDEAL_EQ14_PRE_REVIEW.md` and the frozen `RA10.NuclearNorm`.

The sole public theorem states, for every real scalar and every real `n×n`
matrix including `n=0`, the **frozen sum of all `Fin n` singular values**
of `r • X` equals `|r|` times that same sum for `X`. It uses the exact
`Matrix.toEuclideanLin` scalar bridge. The private proof diagonalizes the
real symmetric Gram operator, tracks sorted eigenvalues under a
nonnegative scalar including ties/zero, identifies the Gram of `r • T`
with `r²` times the original Gram, and takes square roots. This is valid
for negative `r`, for rank-deficient matrices, and for empty dimension.
It introduces no alternate norm, numerical coefficient, hypothesis, or
exceptional order.

The separate imported exact-signature audit
`/private/tmp/ra10-nuclear-homogeneity-independent-audit.lean` at SHA-256
`6250ea5fc8fbfa733b8c989c9ef0f53d3cab9e2736baa510e9dfd40f2fe0efbd`
elaborated the expected signature under pinned Lean 4.33.1 with LeanCert
`kernel` trust. Its `#assert_trust kernel` passed, and `#print axioms`
reported only `[propext, Classical.choice, Quot.sound]`. The source has
no `sorry`, `admit`, `native_decide`, `unsafe`, or new axiom.

This approval covers **homogeneity only**. The two coefficient-one nuclear
ideal inequalities, Eq. (14)'s nuclear bound, pinching, integral transfer,
and the full RA-10 Target remain unproved.
