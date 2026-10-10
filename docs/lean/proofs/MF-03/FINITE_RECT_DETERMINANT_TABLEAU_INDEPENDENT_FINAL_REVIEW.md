# MF-03 finite rectangular determinant/tableau: independent final audit

**Verdict:** APPROVED. Frozen source
`lean-statements/NLA/Proofs/MF03/FiniteRectDetTableau.lean` has SHA-256
`e6e11ca2b94ad996a90e295e854d0eaee211b2c7c17c832f70db4caadab91114`.
Its mathematical precontract at SHA-256
`215bef93c0daf9bc5f2709e2a1cb88ff5ec1b129d3dde04d72beb6e5816f7e43`
was independently approved before implementation.

The source proves the exact Young-diagram equality
`finiteAugShape m 0 = finiteRectShape m`: the augmented bottom row has
length zero. It then specializes the already audited original augmented
determinant/tableau equality at `j=0`, uses the original
`finiteCosineAugDet_zero`, and simplifies the original bottom-cell weight
to the empty product `1`. The resulting public theorem is literally
`finiteCosineRectDet N m = finiteRectTableauSum N m` for all `N,m`, with
the original determinant and original bounded rectangular tableau sum.
Empty domains and `m=0` remain in scope; there is no positivity or
nonzero premise.

The independent imported exact-signature audit is
`/private/tmp/mf03-finite-rect-det-tableau-independent-audit.lean`, SHA-256
`55f591d6d15d03e9ba7e475829e12c7b9ea54f85d8e327f0131a070f3be02fbe`.
Pinned Lean 4.33.1 `lake build NLA.Proofs.MF03.FiniteRectDetTableau`
passed 8,753 jobs; separate `lake env lean` passed both exact signatures
and both `#assert_trust kernel` checks. Both public theorems depend only on
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`,
`native_decide`, unsafe declaration, or new axiom appears in the frozen
module.

The finite rectangular equality is proved. Infinite limits, the original
infinite determinant bound, and the full MF-03 Target remain separate.
