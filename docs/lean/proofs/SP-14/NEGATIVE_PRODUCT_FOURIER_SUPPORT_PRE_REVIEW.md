# SP-14: actual negative product has no nonnegative Fourier modes

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen mathematical pre-implementation contract. Frozen Target: `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. Canonical source: `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, especially endpoint cancellation at lines 765–785 and the negative-frequency split at lines 1362–1368. Parent contract `ENDPOINT_WIENER_CANCELLATION_PRE_REVIEW.md` SHA-256 `6bd5adcd58819b4ad585bb25fd565ee33453c51c341e58e1ccf136a6cbfe9175` was independently approved. Frozen prerequisites pending separate final audits: `RegularizedBaseFactorFourier.lean` SHA-256 `2afdee09ed97dbae6b64529c8a0af23c322ce57619e6b658e3355f52872b64fc` (parent final audit approved) and `NegativeLaurentEndpointDivision.lean` SHA-256 `d4d6fddadfa9d2b306faf88ca03a4cda0391fc59130d89db9ab914c970ffb19b` (pinned direct build passes; parent final audit pending). The actual `baseExteriorFactor`, `negativeLaurent`, and `FourierCoefficient` definitions are used.

## Exact public Lean surface

```lean
theorem baseExterior_negativeLaurent_fourier_nonneg
    (u : ℕ) (p : Fin u → ℝ)
    (hcontact : negativeLaurent u p (-1 : Circle) = 0)
    (k : ℤ) (hk : 0 ≤ k) :
    FourierCoefficient
      (fun s : Circle => baseExteriorFactor s * negativeLaurent u p s) k = 0
```

The theorem quantifies the actual source product `g₀P₋` and the actual normalized interval-integral Fourier coefficient. It derives the support conclusion from the endpoint premise; it does not assume a zero-frequency coefficient field. The continuity of the product follows from audited factor and finite Laurent continuity, so interval-integral linearity applies without totalization ambiguity.

## Exact support calculation

From the separately reviewed finite endpoint division, obtain `q : Fin u→ℝ` with `q_0=0` (if `u>0`) and `P₋(s)=(1+s)Q₋(s)`, where `Q₋=negativeLaurent u q`. Hence `g₀P₋=FQ₋` pointwise, with `F=(1+s)g₀`. Because the `j=0` coefficient of `Q₋` is zero, its nonzero monomials have frequencies `−(j+1)≤−2` for `j≥1`. The Fourier shift identity under the frozen integral is

`FourierCoefficient (fun s => F s * (s:ℂ)^ell) k = FourierCoefficient F (k−ell)`

for continuous `F` and any integer `ell`. For `ell=−(j+1)` and `k≥0`, the shifted frequency is `k+j+1≥2`, where the reviewed `regularizedBaseFactor_fourier` gives zero. Multiply by each real coefficient and sum over the finite `Fin u` set using interval-integral linearity. The `j=0` term is zero even when `k=0`, so all nonnegative modes vanish. No infinite product interchange is needed because `Q₋` is finite.

At `u=0`, the Laurent sum is empty and the conclusion is immediate. At `u=1`, the contact condition forces `p=0`; the derived quotient has zero sole coefficient. For `u=2`, `p=(t,t)` has `Q₋=t s^{-2}`, so `g₀P₋=t F s^{-2}` and its highest mode is `−1`. These are exact for every real `t`, including zero.

This gate proves a Fourier support condition only. The literal weighted Wiener norm of `g₀P₋`, its convolution bound, the other four source smallness inequalities, compatible background inverses, and the frozen negative Target remain open. Do not implement before independent mathematical review of this exact theorem and prerequisite endpoint module final approval. Keep source unimported until a separate source/signature/imported-kernel final audit.
