# SP-14: exact Fourier series of the endpoint-regularized exterior factor

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** source-locked pre-implementation addendum to the independently approved `ENDPOINT_WIENER_CANCELLATION_PRE_REVIEW.md`, SHA-256 `6bd5adcd58819b4ad585bb25fd565ee33453c51c341e58e1ccf136a6cbfe9175`. The frozen negative Target is `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`, and the canonical source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`. The reviewed and frozen `BaseExteriorFactor.lean` SHA is `a8dbc23e8544378ab504ff8130387701fa0270cb2753555c0f05b71057d316dd`. The just-built, separately audit-pending `RegularizedBaseCoeff.lean` SHA is `09aac1a792bbfaf481c94ff2ff2f294bb2ea451afe87d2b3aa9199b34cac4aa6`; implementation of this Fourier gate must wait for its independent final review.

## Exact public Lean signatures

Define the **actual product** of the reviewed boundary factor, not a new independent symbol:

```lean
noncomputable def regularizedBaseFactor (s : Circle) : ℂ :=
  (1 + (s : ℂ)) * baseExteriorFactor s

theorem continuous_regularizedBaseFactor : Continuous regularizedBaseFactor

theorem regularizedBaseFactor_series (s : Circle) :
  regularizedBaseFactor s =
    (s : ℂ) + ∑' n : ℕ,
      regularizedBaseCoeff n * (s : ℂ) ^ (-(n : ℤ))

theorem regularizedBaseFactor_fourier (k : ℤ) :
  FourierCoefficient regularizedBaseFactor k =
    if k = 1 then 1
    else if k ≤ 0 then regularizedBaseCoeff k.natAbs
    else 0
```

The source's Fourier coefficient is the frozen integral `(1/(2π))∫₀^{2π}F(Circle.exp t)e^{-ikt}dt`; no abstract Laurent-coefficient field may replace it. The sign convention gives coefficient `d_n` at frequency `−n`, not `+n`. The single positive term is `s`, so `F₁=1`; the other exact checks are `F₀=d₀=3/2`, `F_{−1}=d₁=3/8`, `F_{−2}=d₂=−1/16`, and `F_k=0` for every `k≥2`. At `s=-1`, the product definition gives `F(-1)=0`, including the square-root contact zero. These integer cases are disjoint and include `k=0`.

Proof route: use unconditional `∑‖c_n‖<∞` to multiply the base series by `1+s`, shift the second summation, and identify the coefficient at `s^{-n}` with `c_n+c_{n+1}`. The resulting series is uniformly absolutely convergent on `Circle`; the reviewed mode integral `FourierCoefficient_circle_mode` and exact interval-integral/sum interchange then give the all-integer Fourier theorem. Continuous additivity is essential because the source Fourier integral is totalized; it holds here. The weighted summability already proved for `d_n` supplies the later `W^{9/8}` norm theorem, but this module need only export the exact series and Fourier coefficients.

The finite endpoint division `P₋=(1+s)Q₋`, bilateral weighted Wiener norm, and product convolution bound remain later stages of the approved parent contract. The actual background Sobolev inverse, conformal map, and original negative Target remain open. This new source must be unimported and separately audited for exact elaborated signature and kernel axioms before integration.
