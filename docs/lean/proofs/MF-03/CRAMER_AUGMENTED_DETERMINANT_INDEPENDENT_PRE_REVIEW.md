# MF-03 Cramer numerator and augmented determinant: independent pre-review

**Disposition:** approved for implementation of the displayed exact theorem. I independently reviewed `CRAMER_AUGMENTED_DETERMINANT_PRE_REVIEW.md` at SHA-256 `3e41367eb3e37a088d8a22fc6d874b1666c689159d2034f9430071fd005952f8`. Its six source locks match the frozen README, manuscript, statement, determinant definition, Toeplitz/Cramer definition, and ratio module.

The source matrix has `T(r,c)=e_(m+r−c)` and RHS `b(r)=−e_(m+r+1)`, with natural-number subtraction interpreted as in the actual Lean definitions. `Matrix.cramer_apply` makes the left side `det (T.updateCol c b)`. After transposition, the replaced column is row `c`; applying the inverse of the cycle `(0 1 … c)` moves that row to row zero, old rows `0,…,c−1` to new rows `1,…,c`, and fixes rows above `c`. The new row zero is the negative of the first row of the **original** `cosineAugDet m (c.val+1)`; rows `1,…,c` have the exact augmented `+1` shift and higher rows have no shift. All subtractions are nontruncating because every row index is below `m`.

The row cycle has sign `(-1)^c` by pinned `Fin.sign_cycleRange`; the RHS minus sign contributes one more factor. Its inverse has the same sign, so the exact coefficient is `(-1)^(c.val+1)`, matching the manuscript's one-based `j=c.val+1`. The theorem needs no determinant positivity, division, finite cutoff, or tableau surrogate. It applies for every `c : Fin m`, including `m=1` and both endpoint columns; the `m=0` instance is vacuous. The original `MF-03` ID and frozen `Target` remain untouched.

Approval is mathematical and source-level only. Freeze the Lean implementation for a separate imported exact-signature, LeanCert-kernel, and axiom audit before aggregate import.
