# SP-14: finite negative Laurent Wiener multiplier and actual product bound

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen mathematical/numerical pre-implementation contract. Frozen negative Target: `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. Canonical source: `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, especially the literal weighted Wiener norm at lines 62–67, endpoint argument at lines 765–785, and the first `g₀P₋` bound at lines 1323–1328. Parent contract `ENDPOINT_WIENER_CANCELLATION_PRE_REVIEW.md` SHA-256 `6bd5adcd58819b4ad585bb25fd565ee33453c51c341e58e1ccf136a6cbfe9175` is independently approved. Frozen kernel-audited prerequisites are `RegularizedFactorWiener.lean` SHA-256 `0cae3d40e5b72928eb4df9a4dfbfe43a52766aebb78a993143411fa0f3432b83`, `NegativeLaurentEndpointDivision.lean` SHA-256 `d4d6fddadfa9d2b306faf88ca03a4cda0391fc59130d89db9ab914c970ffb19b`, and `NegativeProductFourierSupport.lean` SHA-256 `a8bcd7a9c899d52f8a47634fd635a22e57a4643fc4272f00a694942b57aa6cc4` (the last passed parent imported final audit; final review is being written).

## Exact public Lean surface

Use the already frozen `wienerWeight : ℤ→ℝ` and `weightedWienerSize : (Circle→ℂ)→ℝ`, whose Fourier coefficients are the actual normalized interval integrals. Define the finite coefficient size, not a new abstract Wiener norm:

```lean
noncomputable def finiteNegativeWienerSize (u : ℕ) (q : Fin u → ℝ) : ℝ :=
  ∑ j : Fin u,
    wienerWeight (-((j.val + 1 : ℕ) : ℤ)) * ‖(q j : ℂ)‖

theorem negativeLaurent_wiener_eq (u : ℕ) (q : Fin u → ℝ) :
  weightedWienerSize (negativeLaurent u q) = finiteNegativeWienerSize u q

theorem summable_mul_negativeLaurent_wiener
    (f : Circle → ℂ) (hf : Continuous f)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖))
    (u : ℕ) (q : Fin u → ℝ) :
  Summable (fun k : ℤ =>
    wienerWeight k *
      ‖FourierCoefficient (fun s => f s * negativeLaurent u q s) k‖)

theorem weightedWienerSize_mul_negativeLaurent_le
    (f : Circle → ℂ) (hf : Continuous f)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖))
    (u : ℕ) (q : Fin u → ℝ) :
  weightedWienerSize (fun s => f s * negativeLaurent u q s) ≤
    weightedWienerSize f * finiteNegativeWienerSize u q
```

The source-specific corollary should then use the *witness supplied by the actual endpoint equation*:

```lean
theorem baseExterior_negativeLaurent_wiener_bound
    (u : ℕ) (p : Fin u → ℝ)
    (hcontact : negativeLaurent u p (-1 : Circle) = 0) :
  ∃ q : Fin u → ℝ,
    (∀ j : Fin u, j.val = 0 → q j = 0) ∧
    (∀ s : Circle,
      negativeLaurent u p s =
        (1 + (s : ℂ)) * negativeLaurent u q s) ∧
    Summable (fun k : ℤ =>
      wienerWeight k *
        ‖FourierCoefficient
          (fun s => baseExteriorFactor s * negativeLaurent u p s) k‖) ∧
    weightedWienerSize
      (fun s => baseExteriorFactor s * negativeLaurent u p s) ≤
      weightedWienerSize regularizedBaseFactor * finiteNegativeWienerSize u q
```

The generic theorem does not need `q₀=0`; the endpoint quotient has it and thus also yields the separately proved nonnegative-frequency support. The exact equality `negativeLaurent_wiener_eq` makes the finite size the literal Wiener size of the source quotient, with no hidden coefficient-field replacement. The zero-frequency term is counted once. All assertions include `u=0` and `u=1`; both finite sizes are zero when the corresponding Laurent function is zero.

## Mathematical proof and exact checks

For a continuous `f`, finite linearity and the circle-mode shift give

`FourierCoefficient (f · negativeLaurent u q) k = ∑_{j:Fin u} (q_j:ℂ) · FourierCoefficient f (k+j+1)`.

The shift sign is **plus** `j+1` because the quotient monomial has frequency `−(j+1)`. The literal weight `w(k)=(1+|k|)^(9/8)` satisfies

`w(k) ≤ w(k+j+1) w(-(j+1))`.

Indeed `1+|k|≤(1+|k+j+1|)(1+j+1)` by the integer triangle inequality, and real exponent `9/8>0` preserves the inequality. Multiply by `|q_j|·|f̂(k+j+1)|`, sum over all `k∈ℤ`, reindex `k↦k+j+1`, and interchange the **finite** `j` sum with the absolutely convergent integer sum. This proves summability and the constant-one multiplier inequality. Setting `f` to a pure circle mode and using mode orthogonality yields `weightedWienerSize(negativeLaurent u q)=∑_j w(-(j+1))|q_j|`; distinct negative frequencies prevent overlap. For the actual product, the independently reviewed endpoint factorization gives `g₀P₋=FQ₋` pointwise, and the independently reviewed `summable_regularizedBaseFactor_wiener` supplies `hfs`.

Exact checks: `w(0)=1`, `w(1)=w(-1)=2^(9/8)`, `w(-2)=3^(9/8)`. For `u=0`, both `Q₋` and product vanish and all sums equal zero. For `u=1`, the contact premise forces `P₋=Q₋=0`. For the nonempty endpoint example `u=2`, `p=(t,t)`, `q=(0,t)`, the finite quotient size is `3^(9/8)|t|`, and `g₀P₋=tF s^{-2}`. At `k=0`, the shifted factor mode is `F₂=0`; at `k=-1`, it is `F₁=1`. As a weight sanity check with `k=-1`, `j=1`, `w(-1)=2^(9/8)≤w(1)w(-2)=2^(9/8)3^(9/8)`; with `k=-2`, `j=1`, `w(-2)=w(0)w(-2)` is equality.

The denominator-positive and `γ=2^-1000` smallness corollary may be added only after a separate exact contract; the canonical two-level proposition assumes some sufficiently small γ and does not assert this particular choice works for all five bounds. The other four bounds, compatible background inverse maps, conformal map, and full negative Target remain open. This gate is sizeable; implement in separately frozen modules if needed, with independent final source/signature/imported-kernel audit for each. No Lean source before independent mathematical review of this contract.
