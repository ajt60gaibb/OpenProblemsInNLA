# MF-03 nonconstant Padé coefficients: independent pre-review

**Disposition:** approved for implementation of the three displayed exact declarations. I independently reviewed `PADE_NONCONSTANT_COEFFICIENTS_PRE_REVIEW.md` at SHA-256 `ee9fcaf41be2493b9eeed23ecd6646e2532f453af34abffd8ef907fe3e87a462`; all seven source SHA-256 locks match the frozen README, manuscript, statement, and named proof dependencies.

The definition divides the exact original `cosinePadeToeplitz m` Cramer vector by `cosineRectDet m`. The audited equality `det T=cosineRectDet m` and strict positivity provide a nonzero divisor. The audited Cramer vector equation then yields the exact high-degree system `T *ᵥ q=b`, with no substituted matrix or assumed solution. At `m=0`, both vectors are empty and the equation remains valid.

For `c : Fin m`, the one-based exponent `j=c.val+1` lies in `1≤j≤m`. The audited original Cramer identity gives numerator `(-1)^j cosineAugDet m j`; division by the *same* positive original determinant gives the proposed signed ratio with no factor or sign change. The audited ratio theorem has `0≤cosineAugDet m j/cosineRectDet m≤(cosineTail m)^j` with coefficient one. Since `|(-1)^j|=1`, the real absolute value of the actual signed coefficient is exactly the nonnegative ratio, proving the proposed coefficient-one bound. The first and last coefficients and the vacuous `m=0` case retain their correct indices. The constant coefficient `q₀=1`, polynomial construction, Padé numerator and disk Target are separate gates.

Approval is mathematical and source-level only. Freeze any implementation and obtain a separate imported exact-signature, LeanCert-kernel, and axiom audit before aggregate import.
