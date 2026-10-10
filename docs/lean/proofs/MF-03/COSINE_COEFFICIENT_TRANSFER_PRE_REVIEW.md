# MF-03 cosine coefficient transfer: pre-implementation contract

This document specifies a source-locked mathematical and numerical gate after
the independently audited all-complex cosine product identity. It is for
independent review before Lean implementation. It does not change the frozen
`NLA.Statements.MF03.Target`, its canonical README, or any published ID.

## Exact proposed interface

Create a new, initially unimported module
`NLA.Proofs.MF03.CosineCoefficientTransfer`, importing the frozen
`CosineAllComplexProduct.lean`. In namespace `NLA.Proofs.MF03`, define the
real elementary coefficient using **finite subsets** of zero-based factor
indices:

```lean
noncomputable def cosineElementaryCoeff (j : ℕ) : ℝ :=
  tsum (fun s : {S : Finset ℕ // S.card = j} =>
    ∏ k ∈ s.1, cosineFactor (k + 1))
```

Export these two theorems with no added hypotheses:

```lean
theorem cosineProduct_eq_elementarySeries (z : ℂ) :
    tprod (fun k : ℕ =>
      (1 : ℂ) + (cosineFactor (k + 1) : ℂ) * z) =
      tsum (fun j : ℕ => (cosineElementaryCoeff j : ℂ) * z ^ j)

theorem cosineElementaryCoeff_eq_factorial (j : ℕ) :
    cosineElementaryCoeff j =
      (1 : ℝ) / ((2 * j).factorial : ℝ)
```

The second statement is the exact coefficient transfer required by the
manuscript. It includes `j=0`, where the unique empty subset gives `1`.
The type `tprod (fun k => ...)` is definitionally the same product as the
audited all-complex theorem; this spelling also avoids a typed-binder
notation elaboration issue encountered in the previous module.

## Absolute expansion and grouping

Put `a_k = cosineFactor (k+1)`. The reviewed `CosineProduct.lean` proves
`Summable (fun k => a_k)` internally, and the audited
`CosineAllComplexProduct.lean` repeats that argument in a private theorem.
The new module may repeat or package the same proof without editing either
frozen source. Every `a_k` is strictly positive, since `π ≠ 0` and
`k+1−1/2>0`.

For each `z : ℂ`, set `f_z(k)=(a_k : ℂ)*z`. Then
`‖f_z(k)‖=a_k‖z‖`, so `Summable (fun k => ‖f_z(k)‖)` follows from
summability of `a_k`. Pinned
`summable_finsetProd_of_summable_norm` gives absolute summability of

```text
S ↦ ∏ k∈S f_z(k)                  (S : Finset ℕ).
```

Pinned `tprod_one_add` consequently gives

```text
∏' k, (1+f_z(k)) = ∑' S : Finset ℕ, ∏ k∈S f_z(k).
```

The sum is unconditional, including when a product factor vanishes. Reindex
`Finset ℕ` by the explicit equivalence
`S ↔ (S.card, ⟨S, rfl⟩)` with
`Σ j : ℕ, {S : Finset ℕ // S.card=j}`. Absolute summability licenses
the sigma/fiberwise rearrangement into a sum over `j` of sums over
cardinality-`j` subsets. For each such subset, finite product algebra gives

```text
∏ k∈S ((a_k : ℂ)*z) = (∏ k∈S (a_k : ℂ))*z^j.
```

The real fiber sum is summable by restriction of the real nonnegative
finite-subset sum; `Complex.ofReal_tsum` then changes its cast to the complex
fiber sum. Pulling the constant `z^j` through that sum gives precisely
`cosineProduct_eq_elementarySeries`. This step must not infer coefficient
equality from the value identity alone or regroup a merely conditionally
convergent series.

The same grouping at real `r≥0` proves
`Summable (fun j => cosineElementaryCoeff j * r^j)` for every `r`.
In particular, at `r=1` the nonnegative real coefficients are summable.
For completeness, positivity of each fiber term gives
`0≤cosineElementaryCoeff j`; strict positivity for `j>0` follows from
the subset `{0, ..., j-1}`. The `j=0` fiber consists only of the empty
subset, so `cosineElementaryCoeff 0=1`.

## Analytic coefficient uniqueness

The frozen all-complex theorem states that the left side of the expansion
equals `waveSeries z = ∑' j, z^j / ((2j).factorial : ℂ)` for **all**
`z : ℂ`. This establishes equality of the two sums as functions, but a
separate uniqueness argument is required to conclude termwise equality.

One implementable route in pinned Mathlib is to form the scalar formal
multilinear series

```text
p = FormalMultilinearSeries.ofScalars ℂ
      (fun j => (cosineElementaryCoeff j : ℂ)),
q = FormalMultilinearSeries.ofScalars ℂ
      (fun j => 1 / ((2*j).factorial : ℂ)).
```

Summability of the nonnegative `cosineElementaryCoeff j` at `r=1`, together
with `FormalMultilinearSeries.ofScalars_norm` and
`le_radius_of_summable_norm`, gives `1≤p.radius`, hence positive radius.
For `q`, use `Real.summable_pow_div_factorial 1` and the exact factorial
inequality `j!≤(2j)!` to show summability at `r=1`; the same radius lemma
gives `1≤q.radius`. Pinned
`FormalMultilinearSeries.hasFPowerSeriesOnBall` then supplies expansions
near zero. `ofScalars_sum_eq` identifies their sums with the two explicit
power series above. Since both equal `waveSeries` near zero,
`HasFPowerSeriesAt.eq_formalMultilinearSeries` gives `p=q`.
Finally, `FormalMultilinearSeries.coeff_ofScalars` (or
`ofScalars_series_injective`) gives, for each `j`, equality of the complex
coefficients. Injectivity of the real-to-complex cast yields the stated
real equality. An equivalent scalar power-series uniqueness proof is
acceptable if it explicitly supplies a common positive convergence radius.

## Exact index and downstream Schur interface

The manuscript writes factors as `t_ν` for `ν≥1`; here
`t_ν=a_(ν-1)=cosineFactor ν`. Thus `a_0=4/π²` is the `ν=1` factor.
The first coefficients are exact checks:

```text
e_0 = 1,   e_1 = ∑_{k≥0} a_k = 1/2,   e_2 = 1/24.
```

There is no `ν=0` factor, no missing `π` multiplier, and no rounded
constant. In the frozen Padé equation, the coefficient of `z^(j-i)` is
`1/(2(j-i))!`; the second proposed theorem permits replacing it by
`(cosineElementaryCoeff (j-i) : ℂ)` for each `0≤i≤j≤2m`.

The next Schur gate must use the Toeplitz matrix
`T_m(i,j)=e_(m+i-j)` with `i,j=1,...,m`, or the identical zero-based
`Fin m` indexing `e_(m+i-j)`. For `m≥1` these natural indices do not
underflow. Its determinant is `s_(m^m)(a)>0`, and Cramer's rule gives the
normalized denominator coefficient
`q_j=(-1)^j s_(m^m,j)(a)/s_(m^m)(a)` for `1≤j≤m`, with `q_0=1`.
The extra tableau row uses factor indices `k≥m` (equivalently `ν>m`), so
the exact tail is the existing
`cosineTail m = ∑' k, cosineFactor (m+k+1)`.
The required bound remains
`0 < |q_j| ≤ h_j(a_m,a_(m+1),...) ≤ (cosineTail m)^j`.
No Schur, Jacobi–Trudi, tableau, invertibility, or normalized-pair theorem
is asserted by the two proposed exports. The pinned Mathlib source has
tableau infrastructure but no directly available Schur/Jacobi–Trudi
theorem for this infinite-variable specialization; those are separate
formal proof obligations. The existing conditional large-order disk
lemma still needs this denominator bound and normalized-pair existence.

Implementation must use pinned Lean 4.33.1/Mathlib, direct module build,
LeanCert kernel checks, and no proof escape. Do not import a partial new
module into the aggregate or modify the frozen Target before independent
review and a separate final audit.

## Source binding

SHA-256 at pre-review time:

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `docs/lean/proofs/MF-03/ALL_ORDER_SOURCE_OBLIGATIONS.md` | `96399593ee86dedb1020da3f9d9301e865c82eec1c801917edcf587e59a58aa6` |
| `lean-statements/NLA/Proofs/MF03/CosineTail.lean` | `41fc5b7da2f1033b17608a56507aeeba555099f933a1b5eea05477331e8ace8b` |
| `lean-statements/NLA/Proofs/MF03/CosineAllComplexProduct.lean` | `59b6a9cf45df57ae13933abf6aecbbcce47f8c63269f8219b9dcd7cdbd016dbc` |
| Pinned Mathlib `Analysis/SpecialFunctions/Log/Summable.lean` | `7aae0142063f084b5ae999dffb614fd0cdf1e780f648b326f49f36282b4dc81d` |
| Pinned Mathlib `Topology/Algebra/InfiniteSum/Ring.lean` | `3bdb814ce6121ad34c4a8cb0ced54fe8b3ba0106be30e346c9ed3fe2e490ec6b` |
| Pinned Mathlib `Topology/Algebra/InfiniteSum/Constructions.lean` | `3d789b5fa814405e5bcc74a9ab48ce1f5a13dec070550291b6047c3d2c997283` |
| Pinned Mathlib `Analysis/Analytic/OfScalars.lean` | `1823d1130ae0831565bd3d5dbe54b4655933dbd8e93fdec687135c01e2c082e4` |
| Pinned Mathlib `Analysis/Analytic/ConvergenceRadius.lean` | `f6314e1932da1cf3b52545f51ed3c70ab5a5173850aa24d4601aa0d7f1bbfb60` |
| Pinned Mathlib `Analysis/Analytic/Uniqueness.lean` | `3c095cfff0c66f30905355dfe8918c74148cf462427b0b59f5322a495e002424` |

Independent review should verify absolute finite-subset summability,
cardinality grouping, real-to-complex fiber conversion, positive-radius
coefficient uniqueness, factorial and factor indexing, and the exact
`k≥m` tail bridge. This contract makes no Lean proof claim.
