# MF-03 original determinant ratio: independent pre-review

**Verdict:** APPROVED for the displayed exact two-sided ratio signature in
`ORIGINAL_DETERMINANT_RATIO_PRE_REVIEW.md`, SHA-256
`188da8a3dd3aebc5b772900eff289ce5abafbc2c5d8c70f2014ab2baf0c6cc75`.

I independently verified every source lock and the original determinant
and zero-based tail definitions. The already audited coefficient-one
inequality has the exact numerator `cosineAugDet m j` and right side
`cosineRectDet m * (cosineTail m)^j`. The separately audited strict
positivity of the actual original rectangular determinant permits division
without changing the inequality direction, coefficient, exponent, or
denominator.

For the lower sign, the exact finite augmented determinant/tableau identity
and the kernel-proved positive canonical augmented tableau give
`0≤finiteCosineAugDet N m j` whenever `m<N`. This holds eventually for
fixed `m`. The original fixed-size finite-to-infinite determinant limit
therefore yields `0≤cosineAugDet m j`; division by the proven positive
original rectangle gives the proposed nonnegative ratio. This does not
assume positivity or nonvanishing of the augmented determinant in the
target signature. It covers all `m,j` with only `j≤m`, including `m=j=0`
and both extreme values of `j`.

The two-sided exact ratio is mathematically and numerically sound as a
separate gate. Its frozen Lean implementation still requires an independent
imported exact-signature, LeanCert kernel, and axiom audit. Identifying a
Padé coefficient with this signed ratio and proving the full MF-03 Target
remain separate obligations.
