# MF-03 rectangular determinant positivity: independent final audit

**Verdict:** APPROVED. Frozen source
`lean-statements/NLA/Proofs/MF03/RectDeterminantPositivity.lean` has SHA-256
`3b4e0239c569aebf3ac55e71100b7f455d686243a5ea7541b04e4a80dc249ceb`.
Its mathematical precontract was independently approved at SHA-256
`9d509faa59652af32f4440984583e6faa0ed675f7ec9caf6ea3250c78c4ab66c`.

The new `canonicalRectWeight m` is definitionally the original row-constant
tableau's `m×m` product `∏_{r,c<m} cosineFactor(r+1)`, independent of the
cutoff `N`. Every factor is strictly positive; for `m=0`, the empty product
is `1`. The source proves that the audited canonical bounded tableau has
exactly this weight for all `m≤N`, then uses its membership in the original
rectangular tableau sum and nonnegativity of every other original weight.
The audited original finite determinant/tableau equality gives the same
fixed positive lower bound for `finiteCosineRectDet N m`. Since `m≤N`
eventually and the original finite determinants tend to
`cosineRectDet m`, order closedness preserves the fixed lower bound and
proves strict positivity of the original infinite determinant. No finite
enumeration, ratio, desired-positivity premise, or changed weight appears.

The separate imported exact-signature audit is
`/private/tmp/mf03-rect-determinant-positivity-independent-audit.lean`,
SHA-256 `9c73b93a674554c5470388b333e9a08b7708f5b3ae0e5818ed5487f7dcb9be84`.
Pinned Lean 4.33.1 `lake build NLA.Proofs.MF03.RectDeterminantPositivity`
passed 8,758 jobs. Separate `lake env lean` passed the exact definition,
four exact theorem signatures, and all five `#assert_trust kernel` checks.
Each theorem depends only on `[propext, Classical.choice, Quot.sound]`.
No `sorry`, `admit`, `native_decide`, unsafe declaration, or new axiom
appears in the frozen module.

The original rectangular determinant is now strictly positive. Ratio
bounds and the full MF-03 Target remain separate obligations.
