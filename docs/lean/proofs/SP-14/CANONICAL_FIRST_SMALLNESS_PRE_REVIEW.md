# SP-14: the remaining four canonical first-smallness bounds

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen mathematical and exact-numerical pre-implementation contract; no Lean source is authorized by this file until independent review. The frozen negative target is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. The canonical source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, particularly the norm definition near line 710, the two-level proposition and its proof near lines 1314–1385, the explicit-parameter corollary near lines 1670–1765, and the stage budgets near lines 1880–2050. This contract uses the actual `FourierCoefficient` normalized interval integral from the frozen SP-14 statement, the exterior branch `baseExteriorFactor`, and the literal finite Laurent functions and curve in `FiniteLaurentBackground.lean`. The first bound on `g₀P₋` is already proved in frozen `ActualNegativeWienerBound.lean`, SHA-256 `88ecdcd0a7431762eec862ea623a2425884b118ff2fcbc71486159384317d224`; independent final audit/integration of that source is a prerequisite to using it as a reviewed import.

## Exact source quantifiers and scope

The canonical two-level proposition says **there exists a sufficiently small** `γ > 0` such that five strict bounds imply compatible isomorphisms of the *actual* background operator on `H^(-1/4)` and `H^(-1/8)`, with degree-uniform norms and inverse norms. It does not itself name a value of `γ`. A **separate later corollary** states that its quantitative proof permits `γ = 2^(-1000)` and operator/inverse bounds `2^100`. This contract proves only the finite-background Wiener estimates and a nonzero initial two-mode family satisfying all five inequalities for *any supplied* `γ > 0`, hence also for the numerical `2^(-1000)`. It does **not** formalize the two-level proposition, its constant ledger, or the operator isomorphism. In particular, the explicit `γ` corollary cannot be invoked in Lean until its own exact analytic proof is supplied.

The canonical norm is `‖f‖_{W^β} = ∑_{k∈ℤ} (1+|k|)^β |f̂(k)|`, with `f̂(k) = FourierCoefficient f k`, and `β ≥ 0` for every multiplier inequality below. Here `α=1/8`, so `1+α=9/8`. The existing `wienerWeight` and `weightedWienerSize` are exactly the `β=9/8` specialization, not a replacement coefficient norm. All functions in the proposed theorems are continuous, ensuring that finite Fourier linearity uses actual interval integrals rather than an unjustified linearity of totalized integrals.

## Proposed public Lean surface

The signatures below fix the mathematical targets. Tactic-level helper names may vary, but no conclusion or hypothesis may be weakened without another mathematical pre-review. Define once:

```lean
noncomputable def wienerSizeAt (β : ℝ) (f : Circle → ℂ) : ℝ :=
  ∑' k : ℤ, (1 + (k.natAbs : ℝ)) ^ β * ‖FourierCoefficient f k‖

theorem wienerSizeAt_nine_eighths (f : Circle → ℂ) :
  wienerSizeAt (9 / 8 : ℝ) f = weightedWienerSize f
```

The first finite and base-factor gate must prove summability before using a `tsum` as a norm:

```lean
theorem negativeLaurent_W0_eq (u : ℕ) (p : Fin u → ℝ) :
  wienerSizeAt 0 (negativeLaurent u p) = ∑ j : Fin u, |p j|

theorem positiveLaurent_W4_eq (v : ℕ) (p : Fin v → ℝ) :
  wienerSizeAt 4 (positiveLaurent v p) =
    ∑ j : Fin v, ((j.val + 2 : ℕ) : ℝ) ^ 4 * |p j|

theorem baseExteriorFactor_W0_summable :
  Summable (fun k : ℤ => ‖FourierCoefficient baseExteriorFactor k‖)

theorem baseExteriorFactor_W0_le_two :
  wienerSizeAt 0 baseExteriorFactor ≤ 2
```

For the base factor, termwise integration of the already absolutely summable exterior series must identify `ĝ₀(-n)=baseCoeff n` for `n≥0` and `ĝ₀(k)=0` for `k>0`. The coefficient telescope in `BaseCoeffSummable.lean` then gives `∑ₙ ‖baseCoeff n‖≤2`. The exact value 2 is plausible but is **not** required. In `negativeLaurent_W0_eq`, the weights are all 1; in `positiveLaurent_W4_eq`, mode `j+1` has weight `(j+2)^4`.

The endpoint-factor gate is source-specific. For contact data `P₋(-1)=P₊(-1)=0`, use the already reviewed negative quotient `Q₋=negativeLaurent u qMinus` from `negativeLaurent_endpoint_factor`, and prove the positive counterpart with `Q₊=positiveLaurent v qPlus`:

```lean
theorem positiveLaurent_endpoint_factor (v : ℕ) (pPlus : Fin v → ℝ)
    (hcontact : positiveLaurent v pPlus (-1 : Circle) = 0) :
  ∃ qPlus : Fin v → ℝ,
    ∀ s : Circle,
      positiveLaurent v pPlus s =
        (1 + (s : ℂ)) * positiveLaurent v qPlus s
```

The hidden coefficient endpoints must be verified: with one-based coefficients, `p_j=q_j+q_(j-1)`, `q_(-1)=0`, and `q_(v-1)=0`; for `v=0` the family is empty and for `v=1` contact forces `p=q=0`. The exact quotient for `v=2`, `p=(r,r)`, is `q=(r,0)`.

The source's `P₋/g₀` has a removable boundary singularity at `s=-1`; **do not** state equality of totalized complex division there. For a factored negative quotient define the continuous extension

```lean
noncomputable def negativeRatioExtension (u : ℕ) (qMinus : Fin u → ℝ)
    (s : Circle) : ℂ :=
  (s : ℂ) * baseExteriorFactor s * negativeLaurent u qMinus s
```

and prove, for every `s ≠ (-1 : Circle)`, both `baseExteriorFactor s ≠ 0` and

`negativeLaurent u pMinus s / baseExteriorFactor s = negativeRatioExtension u qMinus s`

whenever `P₋=(1+s)Q₋`. At `s=-1` the extension equals 0 and is continuous. The equality follows from `s*g₀(s)^2=1+s`; the nonzero assertion follows from `g₀(s)^2=1+s⁻¹` and `s≠-1`. This extension is the precise continuous interpretation of the ratio used by the source. Its Wiener bound is

```lean
wienerSizeAt 0 (negativeRatioExtension u qMinus) ≤
  wienerSizeAt 0 baseExteriorFactor *
    (∑ j : Fin u, |qMinus j|)
```

The proof requires actual Fourier convolution and constant-one submultiplicativity at exponent 0; multiplication by the mode `s` has exactly unit `W^0` cost. The gate also proves the finite `Q₊` norm at `β=9/8` and the constant-one `W^(9/8)` product inequality for continuous summable functions. No formal Wiener size of a nonintegrable or discontinuous artificial function is substituted.

Write `P=P₋+P₊`, `F=(1+s)g₀=regularizedBaseFactor`, `Q=Q₋+Q₊`, `A=weightedWienerSize F`, and `w₁=2^(9/8)`. The exact curve identity already proved is

`h(s)-s = 2s*g₀(s)*P(s) + s*P(s)^2 = 2s*F(s)*Q(s) + s*P(s)^2`.

For *all* finite `u,v` and real coefficient vectors with separate endpoint contact, prove summability of its `W^(9/8)` Fourier series and

`‖h-s‖_{W^(9/8)} ≤ 2 w₁ A (‖Q₋‖_{W^(9/8)}+‖Q₊‖_{W^(9/8)}) + w₁(‖P₋‖_{W^(9/8)}+‖P₊‖_{W^(9/8)})²`.

This includes `u=v=0`, where both sides are zero. Each `s` shift costs exactly `w₁`; every other factor uses constant-one submultiplicativity. A Lean theorem may package the existential endpoint quotients and the resulting bound together, but it must retain both *separate* contact premises and the actual `finiteBackgroundCurve` on the left.

## Exact two-mode numerical check and simultaneous strict smallness

For `u=v=2`, take `pMinus=(t,t)` and `pPlus=(r,r)` with real `t,r`. Then

`P₋=t(s⁻¹+s⁻²)=(1+s)t s⁻²`, `Q₋=t s⁻²`,

`P₊=r(s+s²)=(1+s)r s`, `Q₊=r s`.

Both contact values at `-1` are **separately** zero. Let `w₁=2^(9/8)`, `w₂=3^(9/8)`, `c=w₁+w₂`, `C₀=‖g₀‖_{W^0}≤2`, and `A=‖F‖_{W^(9/8)}<∞`. The four remaining source bounds, alongside the already proved first bound, specialize exactly or conservatively to

```text
‖P₋‖_{W^0}                = 2|t|,
‖P₊‖_{W^4}                = (2^4+3^4)|r| = 97|r|,
‖P₋/g₀‖_{W^0}             ≤ C₀|t|       (continuous extension),
‖g₀P₋‖_{W^(9/8)}          ≤ A w₂|t|,
‖h-s‖_{W^(9/8)}           ≤ 2w₁A(w₂|t|+w₁|r|)
                               + w₁c²(|t|+|r|)².
```

The coefficient constants 2 and 97 are exact, not estimates from an unspecified `O(·)`. In particular the W4 weights are 16 and 81, and the quotient frequencies are `-2` and `+1`, so their W9/8 weights are `w₂` and `w₁`. The ratio formula is asserted only away from `-1`; the Wiener size is that of its continuous extension.

For a supplied `γ>0`, define the positive finite real number

`D = 1 + 2 + 97 + C₀ + A*w₂ + 2*w₁*A*(w₂+w₁) + 4*w₁*c²`

and take `ε=min(1,γ/(2D))`, `t=r=ε`. Then `ε>0`, all four inequalities above and the fifth `g₀P₋` inequality are **strictly** below `γ`: every linear coefficient is `<D`, while `ε²≤ε` handles the quadratic term, giving each bound at most `Dε≤γ/2<γ`. This proves a genuine nonzero initial finite background for every positive threshold, in particular for the explicitly chosen `2^(-1000)`. It does **not** give the stagewise high-frequency packet estimates, nor the actual operator inverse.

## Feasibility and remaining gates

Implement in this order, each as a separate frozen unimported source for independent final signature/kernel audit: (1) literal W0/W4 finite norms and base `g₀` W0, (2) positive endpoint quotient and continuous negative-ratio extension, (3) constant-one W0/W9/8 products plus actual `h-s` bound, (4) the two-mode strict-`γ` witness. The generic multiplier proof can reuse the previously reviewed negative Laurent multiplier's Fourier-shift method; positive modes require the opposite shift. The first gate is bounded finite algebra plus the already reviewed absolute exterior series; the third is the main Fourier bookkeeping cost. No `lake clean` or shared metadata/identity edit is needed.

The canonical full construction still needs estimates for its growing negative restoring packets and positive packets so that *every stage* stays within the same `γ`, the actual two-level background inverse including compatibility and degree-uniform constants, the nonlinear jet-vector existence at perturbed backgrounds, the infinite limit, both-sided nonextension, and the full negative Target. Proving an initial two-mode background or these Wiener inequalities alone must not be reported as the SP-14 solution.
