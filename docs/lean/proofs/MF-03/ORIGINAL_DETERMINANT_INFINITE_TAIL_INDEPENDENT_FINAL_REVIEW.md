# MF-03 original determinant infinite-tail bound: independent final audit

**Verdict:** APPROVED for both exact coefficient-one determinant bounds.
Frozen source `lean-statements/NLA/Proofs/MF03/OriginalDeterminantInfiniteTail.lean`
has SHA-256 `bd90c1e22cc06a20d7fb94572db30bab46d79fb3a89e5ef282dfc3416c332896`.
The independently approved mathematical precontract has SHA-256
`6471169382a54ae9d92549309d21457082ce4d7fcef71b4d83a91091a62d8e5c`.

The finite theorem replaces the two original bounded tableau sums in the
kernel-proved infinite-tail tableau inequality by their separately audited
original finite augmented and rectangular determinants. Its right side is
the original `finiteCosineRectDet N m * (cosineTail m)^j`, with coefficient
one and tail `Σ' t, cosineFactor(m+t+1)`. No index shift, auxiliary weight,
sign change, division, or extra premise appears. The infinite theorem uses
the original fixed-size determinant limits and
`le_of_tendsto_of_tendsto'` in the correct direction, with the same fixed
tail factor. Both signatures quantify exactly all permitted `N,m,j` or
`m,j` under `j≤m`, including zero and empty cases.

The separate imported exact-signature audit is
`/private/tmp/mf03-original-determinant-infinite-tail-independent-audit.lean`,
SHA-256 `12a1016928cdf44ab558718d6140e4b61f3632273d3736a027368eadeb1a0e14`.
Pinned Lean 4.33.1 `lake build NLA.Proofs.MF03.OriginalDeterminantInfiniteTail`
passed 8,758 jobs. Separate `lake env lean` passed both exact signatures
and both `#assert_trust kernel` checks; both public theorems depend only
on `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`,
`native_decide`, unsafe declaration, or new axiom appears in the frozen
module.

This proves the coefficient-one determinant inequality. Strict positivity
of the rectangular determinant, ratio bounds, and the full MF-03 Target
remain separate obligations.
