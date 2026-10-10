# MF-03 original determinant ratio: independent final audit

**Verdict:** APPROVED for the exact nonnegative, coefficient-one original
determinant ratio. Frozen source
`lean-statements/NLA/Proofs/MF03/OriginalDeterminantRatio.lean` has SHA-256
`6e9399a531f60d6f9098788415f99c1a89232e7197bb25236238b3df86693b55`.
Its exact mathematical precontract was independently approved at SHA-256
`188da8a3dd3aebc5b772900eff289ce5abafbc2c5d8c70f2014ab2baf0c6cc75`.

The helper proves `0≤cosineAugDet m j` for every `j≤m` by taking the
fixed-size limit of the original finite augmented determinants. At all
cutoffs `N≥m+1`, the audited finite determinant/tableau equality and the
kernel-proved positive canonical augmented tableau make the determinant
nonnegative. The ratio theorem divides by the separately audited
strictly positive original `cosineRectDet m`, and uses the audited
coefficient-one infinite determinant inequality in the correct direction.
It retains the exact numerator, denominator, zero-based tail
`cosineTail m`, exponent `j`, and only `j≤m`; `m=j=0` and both extreme
values of `j` remain covered. There is no auxiliary normalization,
numerical cutoff, or assumption that the augmented determinant is nonzero.

The separate imported exact-signature audit is
`/private/tmp/mf03-original-determinant-ratio-independent-audit.lean`,
SHA-256 `9e406f1d56e5d524a9911def3fa0a645991913c3b35bab1e89bb3a47e13f5d16`.
Pinned Lean 4.33.1 `lake build NLA.Proofs.MF03.OriginalDeterminantRatio`
passed 8,761 jobs. Separate `lake env lean` passed both exact signatures
and both `#assert_trust kernel` checks; both theorems depend only on
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`,
`native_decide`, unsafe declaration, or new axiom appears in the frozen
module.

This ratio is a determinant statement. The later signed Padé coefficient
identity, disk estimate, and full MF-03 Target remain separate obligations.
