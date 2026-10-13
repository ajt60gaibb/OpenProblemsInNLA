# MF-03 original determinant infinite-tail bound: independent pre-review

**Verdict:** APPROVED for both displayed exact signatures in
`ORIGINAL_DETERMINANT_INFINITE_TAIL_PRE_REVIEW.md`, SHA-256
`6471169382a54ae9d92549309d21457082ce4d7fcef71b4d83a91091a62d8e5c`.

I independently checked all six source locks and the original determinant
definitions. The finite augmented determinant is the first-`j`-rows-shifted
elementary-coefficient determinant; the rectangle is the original unshifted
determinant. The kernel-proved
`finiteAugTableauSum_le_rect_mul_cosineTail` has coefficient one, exponent
`j`, and the exact infinite tail
`cosineTail m = Σ' t, cosineFactor(m+t+1)`, beginning with zero-based
label `k=m`. The audited original augmented and rectangular
determinant/tableau equalities replace exactly the two tableau sums,
without changing the numerical bound. It covers every `N,m,j` with only
`j≤m`, including `N=0`, `m=0`, `j=0`, and `j=m`.

The existing fixed-`m,j` determinant limit theorems converge respectively
to the original `cosineAugDet m j` and `cosineRectDet m`. Multiplication by
the fixed real `(cosineTail m)^j` is continuous, so closedness of `≤`
passes the finite coefficient-one inequality in the same direction to
the original infinite determinants. This limit step needs no sign
assumption on either determinant, no division, and no finite-order
enumeration. Positivity and any ratio formula remain separate.

The proposed exact signatures are mathematically and numerically sound.
Each implemented stage still requires a frozen source, independent imported
exact-signature LeanCert kernel/axiom audit, and aggregate import. The full
MF-03 Target remains open.
