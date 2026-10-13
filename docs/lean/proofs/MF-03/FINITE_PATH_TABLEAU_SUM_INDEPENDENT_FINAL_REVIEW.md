# MF-03 finite path/tableau weighted sum: independent final review

**Verdict:** APPROVED as the original finite weighted-sum transport stage.
The source `lean-statements/NLA/Proofs/MF03/FinitePathTableauSum.lean` is
frozen at SHA-256 `cdbe571fc050c281941a9fe97d3a1bb1f03eb9c03845cf01296c78c50e321ad4`.
The source-locked approved contract remains
`FINITE_WEIGHTED_TABLEAU_TRANSPORT_PRE_REVIEW.md` at SHA-256
`8aa1a84c3925ebd46e4bcbd9c8bad0a2ff961f3fa8543a111b1c6a24a8600241`.

The equivalence is definitionally the composition of the previously audited
literal valid-path-to-column-system and column-system-to-augmented-tableau
equivalences. The theorem equates the original `finiteValidPathSum m N` at
the original endpoints with the original `finiteAugTableauSum N m j`, for
every `N,m,j` with `j≤m`. Its `Fintype.sum_equiv` proof uses the separately
audited pointwise weight equality; it does not change either summand, insert
a sentinel factor, or assume nonempty domains. Thus `m=0`, `N=0,m>0`,
`j=0`, and `j=m` are included in the same exact signature.

The independent imported exact-signature audit is
`/private/tmp/mf03-finite-path-tableau-sum-independent-audit.lean`, SHA-256
`a96f12a9fbf76a236ab58496cb900723da9385f1981916df46f5d2c5ff969f45`.
Pinned Lean 4.33.1 `lake build NLA.Proofs.MF03.FinitePathTableauSum` passed
8,751 jobs; separate `lake env lean` passed the exact composition equation,
the exact original weighted-sum signature, and both `#assert_trust kernel`
checks. Both declarations have only `[propext, Classical.choice, Quot.sound]`
as axioms. No `sorry`, `admit`, `native_decide`, unsafe declaration, or new
axiom appears in the frozen module.

This gate proves the finite sum equality. The original determinant/tableau
equality, positivity, and full MF-03 Target require separate reviewed proofs.
