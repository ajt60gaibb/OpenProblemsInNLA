# SP-14: actual endpoint vanishing for every weighted input

**Status:** source-locked mathematical and exact-index pre-implementation contract for independent review. **Author:** `/root/sp14_base_proof`, 10 October 2026. No Lean source for this gate has been written.

## Source locks and target scope

| Source | SHA-256 |
| --- | --- |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Canonical `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| `EndpointBaseSeries.lean` | `69ecc4eb22321a753dbc4dd69a358734ff12ee79a9ac4a2a04cd63da2bc562cd` |
| `WeightedSobolevOperators.lean` | `f0368eb90ab2af9bdbdce1405c1bae511e4c1868ff95015d575cde65fd07b0f1` |
| `EndpointCircleCoeffSummable.lean` | `f6d282cca32941a84dbbbe0f2608d72ee971d2355ce70cd87a5b0fc1489bedd2` |
| `EndpointNegativeOperator.lean` | `16685a4f52b47911d79fc79b78cbdd9117e3efcb914e5102e0b068da118442b1` |
| `EndpointFiniteRealizationPointwise.lean` | `60dd3e510970fcc241ab2f535a987d53cd642f936f9daef0ad41b37cc4d0b6b1` |

The canonical source's endpoint-extension lemma says that for `r>1/2`, its continuous representative vanishes at `-1`. The audited `endpointCircleRealization` is the actual two-sided circle series with the frozen Fourier integral. This gate proves exactly that endpoint statement for the present `1/2<r<1` range. It does not claim the full source lemma's `0<r<1` mapping range or the final negative `Target`.

## Exact public Lean conclusions

Use `(-1 : Circle)` as the endpoint; its complex coercion is `-1`. No division by the base symbol is allowed there.

```lean
theorem endpointBaseSymbol_sq (z : Circle) :
    endpointBaseSymbol z ^ 2 = 1 + (z : ℂ)⁻¹

theorem endpointBaseSymbol_neg_one :
    endpointBaseSymbol (-1 : Circle) = 0

theorem sobolevTruncation_tendsto (r : ℝ) (y : SobolevCoeff r) :
    Filter.Tendsto (fun N : ℕ => sobolevTruncation r N y)
      Filter.atTop (nhds y)

theorem endpointCircleRealization_pointwise_norm_le
    (r : ℝ) (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (z : Circle) :
    ‖endpointCircleRealization r hrHalf hr1 y z‖ ≤
      ‖endpointCircleWeightLp r hrHalf‖ *
        (1 + endpointSchurConstant r) * ‖y‖

theorem endpointCircleRealization_neg_one_zero
    (r : ℝ) (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) :
    endpointCircleRealization r hrHalf hr1 y (-1 : Circle) = 0
```

The norm bound is a useful exposed intermediate. Its literal `endpointSchurConstant r` is `1+1/r+1/(1-r)`, already audited; `endpointCircleWeightLp` has coordinates `(n+1)^(-r)` and is in `ℓ²` exactly because `r>1/2`. The theorem may be split into separately audited modules (square/zero, truncation density, pointwise bound, endpoint limit) while retaining these public signatures. Proving the limit through a direct summable-series argument instead of the displayed pointwise bound is acceptable only if the bound is still proved as stated, since it is part of this contract.

## Mathematical proof obligations

1. **Exact exterior square and boundary zero.** Let `a_n=baseCoeff n` and `F_z(n)=a_n(z:ℂ)^(-n)`. The audited `summable_norm_baseCoeff` makes `F_z` absolutely summable on every circle point. The Cauchy product and audited `baseCoeff_convolution` give coefficient `1` at `n=0`, coefficient `1` at `n=1`, and `0` for every `n≥2`; hence `g₀(z)^2=1+z⁻¹`. At `z=-1`, the square is zero and therefore `g₀(-1)=0`. This argument identifies the normalized already-defined series and uses no arbitrary square-root choice.
2. **Exact finite support and density.** For `T_N=sobolevTruncation r N`, the audited coordinate theorem gives `(T_N y)_k=y_k` for `k<N`, zero for `k≥N`, including `N=0`. The finite sum `∑_{k<N} lp.single 2 k (y_k)` equals `T_N y` coordinatewise. Pinned Mathlib's `lp.hasSum_single` with `p=2≠∞`, followed by natural-range convergence, gives `T_N y→y` in the literal weighted `lp 2` norm; no external Sobolev density surrogate is introduced.
3. **Pointwise operator bound.** For any `z`, both mode factors `(z:ℂ)^n` and `(z:ℂ)^(-(n+1):ℤ)` have norm one. Hölder's audited `lp.tsum_mul_le_mul_norm` at `p=q=2` bounds the positive series by `W_r‖y‖`, where `W_r=‖endpointCircleWeightLp r hrHalf‖`. It bounds the negative series by `W_r‖endpointNegativeOperator r (by linarith) hr1 y‖`. The audited operator norm bound gives `≤W_r C_r‖y‖`. Summing yields exactly `W_r(1+C_r)‖y‖`. Prove complex linearity of `y↦endpointCircleRealization … y z` (finite/infinite sums with audited absolute summability and the negative CLM), or prove directly the corresponding difference bound; either makes evaluation continuous in the input. Continuity in the circle variable alone is insufficient for this density step.
4. **Pass the finite identity to the endpoint.** The reviewed pointwise theorem gives `endpointCircleRealization … (T_N y) (-1)=g₀(-1)·endpointFiniteInverse … (T_N y) N (-1)=0` for each `N`, using the actual support condition. The pointwise difference bound and `T_N y→y` imply `endpointCircleRealization … y (-1)=0`. The proof must use the literal `endpointCircleRealization`, not an assumed `g₀V` at infinite input; no infinite inverse polynomial is needed.

## Exact endpoint and numerical checks

- At `N=0`, `T_0 y=0`, the finite polynomial is the empty sum, and its endpoint value is zero.
- At `N=1`, only the physical coefficient `a_0` remains; `V_1=a_0`, so `g₀(-1)V_1(-1)=0`, even when `a_0≠0`.
- At `N=2` for a physical unit coefficient at mode `1`, `V_2(z)=z-1/2`; its value at `-1` is exactly `-3/2`, yet `g₀(-1)V_2(-1)=0`. This checks that the proof does not divide by `g₀(-1)`.
- At `r=3/4`, the literal Schur constant is `C_r=1+4/3+4=19/3`. The weight norm satisfies `W_r²=∑_{n≥1}n^{-3/2}≤3` by the exact integral comparison, giving the optional bound `W_r(1+C_r)≤(22/3)√3`. This numerical check is an exact upper bound, not a substitute for the symbolic Lean theorem.

This gate establishes one necessary base-endpoint property. It leaves `‖V‖_{L²}` and its infinite extension, perturbed Cauchy projection inverses, source's nonlinear jet stages, both-sided nonextension of the final packet symbol, selected-section multiplicities, and the canonical gap open. All frozen statements, targets, identities, and catalog files remain unchanged. Implementation requires independent pre-review and separate imported LeanCert kernel/signature audits for each frozen source.
