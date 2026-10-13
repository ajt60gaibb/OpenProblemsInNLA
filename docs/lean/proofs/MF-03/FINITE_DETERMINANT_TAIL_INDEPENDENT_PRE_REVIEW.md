# MF-03 finite determinant tail: independent mathematical pre-review

**Verdict:** APPROVED for the displayed exact Lean signature in
`FINITE_DETERMINANT_TAIL_PRE_REVIEW.md`, SHA-256
`2ec1614422094812aac5ee2af42d33396147fb674497a33cda36efbab8578d20`.

I independently checked every source lock in the contract against the
current original MF-03 README, frozen statement, finite determinant,
tableau tail-bound, and now audited determinant/tableau module. The left
side `finiteCosineAugDet N m j` is the original determinant with its first
`j` rows shifted. The right side is the original rectangular tableau sum
times the `j`th power of the exact finite tail over zero-based labels
`m≤k<N`, with factor `cosineFactor(k+1)`. The coefficient is exactly one;
there is no normalization, absolute value, division, or changed index.

The already kernel-proved
`finiteCosineAugDet_eq_augTableauSum N m j hj` and
`finiteAugTableauSum_le_rect_mul_tail N m j hj` have literally matching
middle terms and the same only hypothesis `j≤m`. Their composition proves
the proposed inequality for all `N,m,j`, including `m=0`, `j=0`, `j=m`,
and `N=0`; empty products and sums are handled in the imported theorems.
No denominator positivity is needed.

This approval is for the finite numerical inequality only. A frozen Lean
implementation still requires a separate exact-signature, LeanCert kernel,
and axiom audit before import. The infinite determinant ratio, denominator
positivity, and full MF-03 Target remain open.
