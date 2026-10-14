# SP-14 negative product Fourier support: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen exact contract for implementation. It proves absence of nonnegative Fourier modes of the actual product `g₀P₋` from actual contact, without claiming a Wiener bound or the SP-14 Target.

| Reviewed input | SHA-256 |
| --- | --- |
| `NEGATIVE_PRODUCT_FOURIER_SUPPORT_PRE_REVIEW.md` | `523cbf9b7b9b478367459a99b0cff7768a8f1df4ea6edaea6e046fe038269dc0` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Audited regularized factor Fourier source | `2afdee09ed97dbae6b64529c8a0af23c322ce57619e6b658e3355f52872b64fc` |
| Audited endpoint division source | `d4d6fddadfa9d2b306faf88ca03a4cda0391fc59130d89db9ab914c970ffb19b` |

The reviewed endpoint factorization gives `P₋=(1+s)Q₋` with `Q₋=Σ_{j∈Fin u}q_j s^{-(j+1)}` and `q₀=0` whenever that index exists. Hence `g₀P₋=FQ₋` pointwise for the actual `F=(1+s)g₀`. The frozen normalized interval integral has the exact shift identity `FourierCoefficient(F·s^ell,k)=FourierCoefficient(F,k−ell)`; for `ell=−(j+1)` and `k≥0` the shifted frequency is `k+j+1`. If `j≥1`, this is at least two, where the audited Fourier theorem gives zero. If `j=0`, the real scalar coefficient itself is zero, including at `k=0`. Finite sum linearity is legitimate because the factor and monomials are continuous; no infinite coefficient rearrangement is needed.

The `u=0` case has an empty product and integral zero. At `u=1`, contact forces a zero source correction. At `u=2` with `p=(t,t)`, the derived quotient is `t s^{-2}`, so `FQ₋` has highest frequency `−1`; this checks the edge case for every real `t`. The proposed public theorem quantifies the actual `negativeLaurent`, the actual `baseExteriorFactor`, every nonnegative integer mode, and the source contact condition. The shift sign and index cutoff are exact.

Implementation must prove the shift under the frozen integral, finite linearity, and all `Fin u` cases, and keep the source unimported until a separate source/signature/LeanCert audit. Weighted convolution, the remaining source smallness estimates and final counterexample remain open.
