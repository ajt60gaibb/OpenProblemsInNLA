# MF-03 finite path/tableau pointwise weight: independent final review

**Verdict:** APPROVED as the exact pointwise weight stage only. The source
`lean-statements/NLA/Proofs/MF03/FinitePathTableauWeight.lean` is frozen at
SHA-256 `3af20256989f06f7f0d9d7ea14ab698975c683728adc7664538e7aac7163bc33`.
The approved mathematical/indexing contract
`FINITE_WEIGHTED_TABLEAU_TRANSPORT_PRE_REVIEW.md` retains SHA-256
`8aa1a84c3925ebd46e4bcbd9c8bad0a2ff961f3fa8543a111b1c6a24a8600241`.

I independently compared both public declarations with the original
`finiteRectWeight`, `finiteBottomWeight`, and `finiteValidPathWeight`, and the
audited actual-label and path-label identities. The first declaration sums
each original upper row `r<m` across every column `p<m`, and the genuine
bottom row only at `p<j`. Its `finiteTableauActualLabels_product` premise
erases the short-column sentinel `N`. The second declaration uses the literal
`finitePathToColumnSystem` followed by `finiteColumnSystemToTableau`; its
factor is exactly `cosineFactor(k+1)` for each zero-based advance label.
No sentinel, extra factor, normalization, positivity premise, or cancellation
appears. The formulas cover all `N,m,j` with `j≤m`, including empty shapes,
`j=0`, `j=m`, and empty path/tableau domains.

The independent imported exact-signature audit is
`/private/tmp/mf03-finite-path-tableau-weight-independent-audit.lean`,
SHA-256 `eb079721780cde34d1531e1e81f94dc65658e0fae90f168c33dc304eed8effc9`.
Pinned Lean 4.33.1 `lake build NLA.Proofs.MF03.FinitePathTableauWeight`
passed 8,750 jobs, and `lake env lean` on the separate audit passed both
exact-signature examples and both `#assert_trust kernel` checks. Both public
theorems depend only on `[propext, Classical.choice, Quot.sound]`. The frozen
module contains no `sorry`, `admit`, `native_decide`, unsafe declaration, or
new axiom.

This stage proves only pointwise weight preservation. Finite sum reindexing,
the determinant/tableau identity, positivity, and the full MF-03 Target remain
open for their own reviewed gates.
