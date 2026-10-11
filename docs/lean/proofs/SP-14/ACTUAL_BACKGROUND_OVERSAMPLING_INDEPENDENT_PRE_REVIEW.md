# SP-14 actual-background oversampling: independent mathematical and numerical pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen contract for incremental Lean implementation. This approval concerns the exact source operator and numerical gate; it is not a proof of its analytic hypotheses or the frozen negative target.

| Reviewed input | SHA-256 |
| --- | --- |
| `ACTUAL_BACKGROUND_OVERSAMPLING_PRE_REVIEW.md` | `5b52aaf4103ac675f74797cbd17ba63c39fdca5556b5203076c15a5cd889db68` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Audited abstract `SobolevOversampling.lean` | `fd9b5a433847dc8392070752a97244bebeedde08d4d7f7a198e24d64f6f27d77` |
| Audited physical and operator modules | `ea0166080ec91c5df4da14e2f38eca5fc2a7f9271866099aad1fb8f46e5ba109`; `f0368eb90ab2af9bdbdce1405c1bae511e4c1868ff95015d575cde65fd07b0f1` |

The five strict smallness assumptions and finite real Laurent-background conditions match the source's two-level isomorphism proposition. In particular, `P₋/g₀` and `g₀P₋` carry different norms and cannot be collapsed into a single perturbation field. The limiting Jacobian formula is the source's coefficient extraction `−2∑_d v_d[s^d]R_tX_t`, and the displayed inverse preconditioner has its exact `−1/2`, binomial `−1/2`, and `1/(k+1)` factors. The contract correctly requires the polynomial operator `𝒜_g=(𝒥_g(J⁰)⁻¹·)∘f` to be related to the exact boundary-integral form, then extended to the **specific** physical weighted sequence spaces. It requires both-sided inverses and compatibility, with all four source bounds `≤2^100`; merely assuming an abstract isomorphism would prove only the already audited algebra.

The parameter selection matches the canonical explicit corollary: `s=−1/4`, `τ=1/8`, `s+τ=−1/8`, `σ=3/8`, and `θ=2^−10000<θ₀=2^−20`. For positive `m`, `h_m=⌊θm⌋≤θm`, while `q_m+1=⌊σm⌋+1>σm`; hence `h_m/(q_m+1)<θ/σ=(8/3)θ<4θ`. Monotonicity of floor gives `h_m≤q_m`; `m=0` has `h_m=q_m=0` and ε₀=0. The abstract theorem's `q+1` and `h` estimates then yield exactly `ε_m=2^200(h_m/(q_m+1))^(1/8)`, and its five advertised right-inverse conclusions have the source's operator order. Since `ε_m<1/2`, the bound `2^100/(1−ε_m)<2^101` follows without changing the target constant.

I independently recomputed the numerical ledger with exact integer and rational arithmetic. `2^100γ=2^−900`; multiplying by the bare inverse bound `2^40` gives `2^−860<1/2`; the other Neumann test is `2^25γ=2^−975<1/2`. For `u=2^200(4·2^−10000)^(1/8)`, `u^8=2^−8398<2^−8=(1/2)^8`, so `u<1/2` by monotonicity on nonnegative reals. At the first nonzero retained row count, `m=2^10000`, the exact floors are `h_m=1`, `q_m=3·2^9997`, and `h_m/(q_m+1)<(8/3)2^−10000<4·2^−10000`. These checks validate the exponent arithmetic and floor endpoints, not the analytic operator estimates.

The primary theorem may be split into smaller audited lemmas for the Wiener/Cauchy estimates, conformal map, Jacobian identity, endpoint extensions, perturbation, and inverse compatibility. Each intermediate must retain the actual background and operator meaning. The source's analytic chain is substantial; no existing Lean file proves it. Forcing, finite Jacobian replacement, nonlinear correction, infinite symbol, two-sided nonextension, spectral gap, and `NLA.Statements.SP14.Target` remain open. Every future frozen Lean module needs a separate exact-signature, proof-escape, imported LeanCert kernel, and transitive-axiom audit. Changed contract bytes reopen this review.
