# SP-14 finite negative Laurent Wiener multiplier: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen exact contract for implementation. It gives a constant-one finite multiplier estimate for the literal bilateral `9/8`-weighted Wiener size and applies it to the actual contact-corrected product; the nonlinear Target remains open.

| Reviewed input | SHA-256 |
| --- | --- |
| `FINITE_NEGATIVE_WIENER_PRODUCT_PRE_REVIEW.md` | `96e380a841054940a4ac07ffbee67dcef4eac45efac75979fcf991e5c82bad9d` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Audited regularized factor Wiener source | `0cae3d40e5b72928eb4df9a4dfbfe43a52766aebb78a993143411fa0f3432b83` |
| Audited negative product support source | `a8bcd7a9c899d52f8a47634fd635a22e57a4643fc4272f00a694942b57aa6cc4` |

For any continuous `f`, finite linearity and the frozen integral's monomial shift give `\widehat{fQ}(k)=Σ_{j∈Fin u}q_j\widehat f(k+j+1)`. The plus sign is exact because the quotient has frequency `−(j+1)`. The literal weight `w(k)=(1+|k|)^(9/8)` satisfies `w(k)≤w(k+j+1)w(−(j+1))`: integer triangle inequality gives the base inequality and the positive real exponent preserves products and order. Absolute summability of the weighted coefficients of `f` allows the integer reindex and finite `j` sum interchange, proving both summability and the constant-one bound.

The finite quotient's strict negative modes are distinct, so pure-mode orthogonality under the actual integral gives exact equality of its Wiener size with `Σ_jw(−(j+1))|q_j|`. The zero-frequency term in the bilateral norm is counted once. The source-specific corollary uses the **derived** endpoint quotient `P₋=(1+s)Q₋`, pointwise `g₀P₋=FQ₋`, and the audited finiteness of `F`. It does not assume an abstract quotient or replace integral coefficients by a formal field.

At `u=0` and contact-constrained `u=1`, the finite size and product vanish. For `u=2,p=(t,t)`, `q=(0,t)` gives size `3^(9/8)|t|`; the product's highest frequency is `−1`, consistent with the separate support theorem. The contract correctly defers a numeric γ threshold and the other smallness conditions. Implementation may split the exact generic and source-specific theorems into independently audited modules. Keep all new sources unimported until signature and LeanCert kernel review.
