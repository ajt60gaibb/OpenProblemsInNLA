# MF-03 finite determinant tail: independent final audit

**Verdict:** APPROVED for the exact coefficient-one finite determinant bound.
Frozen `lean-statements/NLA/Proofs/MF03/FiniteDeterminantTail.lean` has
SHA-256 `30fc19ef390d4098ce462a26a53504879b2d861f52286bd0565f8134d3c90a84`.
The mathematical precontract was independently approved at SHA-256
`2ec1614422094812aac5ee2af42d33396147fb674497a33cda36efbab8578d20`.

The source signature is literally
`finiteCosineAugDet N m j ≤ finiteRectTableauSum N m *
(finiteCosineTail N m)^j` for all `N,m,j` under only `j≤m`. The proof
composes the audited original determinant/tableau equality with the
already kernel-proved augmented-tableau tail inequality. It preserves the
original determinant, rectangular sum, zero-based tail over `m≤k<N`,
factor `cosineFactor(k+1)`, exponent `j`, and coefficient one. Empty and
extreme cases remain quantified; no nonzero denominator or positivity
premise is introduced.

The independent imported exact-signature audit is
`/private/tmp/mf03-finite-determinant-tail-independent-audit.lean`, SHA-256
`fa65b39b6156ca8471680d55a547af7b89321f19d6213519902949a7a6c8a3e9`.
Pinned Lean 4.33.1 `lake build NLA.Proofs.MF03.FiniteDeterminantTail`
passed 8,756 jobs; separate `lake env lean` passed the exact signature and
`#assert_trust kernel`. The theorem depends only on `[propext,
Classical.choice, Quot.sound]`. No `sorry`, `admit`, `native_decide`, unsafe
declaration, or new axiom appears in the frozen module.

The bound still has the rectangular tableau sum on the right. The original
rectangular determinant identification, infinite limit, denominator
positivity, and full MF-03 Target require separate gates.
