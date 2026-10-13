# SP-14: finite background correction acting on the completed endpoint inverse — pre-implementation contract

## Source and dependency locks

- Frozen target: `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. Its negative `Target` is unchanged.
- Canonical source: `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`. Use the endpoint-extension lemma at lines 856–902 and the actual finite background and one-sided density-product argument at lines 1316–1385.
- Audited completed inverse: `lean-statements/NLA/Proofs/SP14/EndpointInverseL2Completion.lean`, SHA-256 `e26a35419e34a7cd3bf304ee1cddab1b4d452328375baf2495ec9bb802091586`. Its `endpointInverseL2` is the completion of the **actual triangular finite inverse**, with `endpointInverseL2_norm_le` and the exact constant `endpointInverseHSBound r = 1 + 1 / (r - 1/2)`.
- Audited actual finite background: `lean-statements/NLA/Proofs/SP14/FiniteLaurentBackground.lean`, SHA-256 `21ddde26cfbbfec236f7c9ddc3b212702baa56c0ceef333e9289f09f5a052e7b`. Here `finiteLaurentCorrection u v pMinus pPlus = P_-+P_+` with exactly the negative exponents `-(j+1)` and positive exponents `j+1`, and `finiteBackgroundFactor = baseExteriorFactor + finiteLaurentCorrection`.
- Audited coefficient/Wiener identities: `lean-statements/NLA/Proofs/SP14/CanonicalFirstWienerSizes.lean`, SHA-256 `b640412b39b505a795f70ab59cdd0f18bb3b006c5f8afdc29e4db1dc53ab78f8`; its `negativeLaurent_W0_eq` and `positiveLaurent_W4_eq` identify the source's actual norms with the finite coefficient sums.

## Exact next gate

This gate bounds the correction term `P V` for the **actual** finite Laurent background, with `V = endpointInverseL2 r hrHalf y` in probability-Haar `L²` on `AddCircle (2π)`. It is the first quantitative interaction of the completed base inverse with the perturbed factor `g = g₀ + P`; for finite polynomial inputs the algebraic expansion is `g V = g₀ V + P V`. The present gate asserts the bound for `P V` only. It does not yet construct the actual perturbed operator `𝒜_g`, its inverse, or the nonlinear counterexample.

In a new, unimported module under `NLA.Proofs.SP14`, with `set_option autoImplicit false` and `set_option leancert.trust "kernel"`, the exact proposed public signatures are:

```lean
theorem finiteLaurentCorrection_norm_le_coeffSum
    (u v : ℕ) (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ)
    (s : Circle) :
    ‖finiteLaurentCorrection u v pMinus pPlus s‖ ≤
      (∑ j : Fin u, |pMinus j|) + (∑ j : Fin v, |pPlus j|)

theorem finiteLaurentCorrection_endpointInverseL2_energy_le
    (r : ℝ) (hrHalf : (1 / 2 : ℝ) < r)
    (u v : ℕ) (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ)
    (y : SobolevCoeff r) :
    (∫ θ : AddCircle (2 * Real.pi),
       ‖finiteLaurentCorrection u v pMinus pPlus (AddCircle.toCircle θ) *
         endpointInverseL2 r hrHalf y θ‖ ^ 2
         ∂AddCircle.haarAddCircle) ≤
      ((∑ j : Fin u, |pMinus j|) + (∑ j : Fin v, |pPlus j|)) ^ 2 *
        endpointInverseHSBound r ^ 2 * ‖y‖ ^ 2
```

The additive circle's Haar measure is its **probability** Haar measure of period `2π`; no factor `2π` or interval normalization may be inserted. Evaluation of an `Lp` class in the displayed integral means any representative and the inequality is invariant under almost-everywhere equality. The proof must show that the integrand is integrable, using the bounded continuous Laurent multiplier and the completed `L²` inverse. No pointwise value of a general `L²` class is claimed. If pinned Lean requires explicit coercion or measure notation for the representative, an elaboration-only signature correction must receive a written addendum before final audit; the mathematical assertion and quantifiers must remain identical.

## Mathematics and exact numerical checks

On the unit circle, each integer power of `s` has modulus one, including every negative power. The triangle inequality gives `‖P(s)‖ ≤ A`, where `A = ∑|pMinus| + ∑|pPlus|`. Hence `‖P(s)V(θ)‖² ≤ A²‖V(θ)‖²` almost everywhere. Probability-Haar `Lp` norm identity and `endpointInverseL2_norm_le` give `∫‖V‖² ≤ B_r²‖y‖²`, where `B_r=1+1/(r−1/2)`. Both factors are nonnegative, so the displayed conclusion follows with no hidden constant.

- `u=v=0`: `P=0`, `A=0`, and the integral is exactly zero.
- `u=v=1`: `P(s)=a s⁻¹+b s`; at `s=1`, the bound is `|a+b|≤|a|+|b|`, with equality when `a,b≥0`. This checks both exponent orientations and the sharp coefficient sum.
- `r=3/4`: `B_r=5`, giving the exact energy coefficient `25 A²`.
- `r=7/8`: `B_r=11/3`, giving the exact energy coefficient `(121/9) A²`.
- If the source's separate actual conditions `‖P_-‖_{W⁰}<γ` and `‖P_+‖_{W⁴}<γ` hold, then `A<2γ` because each positive weight `(j+2)^4≥1`. The energy coefficients are strictly below `100γ²` and `(484/9)γ²` at the two respective values of `r`. The two-level proposition only quantifies **some sufficiently small** `γ>0`; the later explicit `2^-1000` is a chosen sufficient threshold, not the proposition's fixed constant.

## Proof and scope audit

The first theorem is finite-sum triangle inequality plus `Circle.abs_coe`, including empty sums. The second requires a bounded-multiplier estimate on `Lp ℂ 2` for the exact `AddCircle.toCircle` pullback, the probability-Haar `L²` norm-square identity, and the audited `endpointInverseL2_norm_le`. Its result concerns only `P V`, not `g V` as a completed `L²` object. The later decomposition `g V = E y + P V` needs a separate finite-truncation/limit theorem because `V` is only an `L²` equivalence class. The actual `R/h'` multiplier, Cauchy projection, compatible `H^{-1/4}`/`H^{-1/8}` inverse, canonical gap, and both-sided nonextension remain open.

No Lean source is to be written before independent mathematical/numerical review of this frozen contract.
