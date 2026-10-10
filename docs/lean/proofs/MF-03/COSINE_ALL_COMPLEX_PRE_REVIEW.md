# MF-03 all-complex cosine product: pre-implementation contract

This contract specifies the next analytic bridge after the reviewed dense-set
cosine product. It is for independent mathematical and numerical review before
any Lean implementation. It changes neither the frozen `NLA.Statements.MF03.Target`
nor the canonical MF-03 problem.

## Exact proposed interface

In a new, initially unimported `NLA.Proofs.MF03.CosineAllComplexProduct` module,
import the frozen `CosineDenseProduct.lean`. Export the following two theorems in
namespace `NLA.Proofs.MF03`:

```lean
theorem cosineFactor_tprod_eq_waveSeries (z : ℂ) :
    (∏' k : ℕ, (1 : ℂ) + (cosineFactor (k + 1) : ℂ) * z) =
      waveSeries z

theorem cosinePartialProduct_tendsto_waveSeries (z : ℂ) :
    Filter.Tendsto
      (fun N : ℕ => cosinePartialProduct N z)
      Filter.atTop (nhds (waveSeries z))
```

Both statements quantify over **every** `z : ℂ`, including the values
`z = -(πw)^2` for integer `w`. Neither adds a premise to the frozen Padé
Target. The `tprod` uses the same `k = 0, 1, ...` factors as the existing
finite product; there is no `k = -1` or `ν = 0` factor.

## Continuity and exceptional-set argument

Write `a_k = cosineFactor (k + 1) = 1/[π²(k+1/2)²]` and
`T(z) = ∏' k, (1 + a_k z)`. The existing
`cosineFactors_multipliable z` proves the product exists for each complex
`z`. To extend its value through the excluded sine zeros, prove the auxiliary
claim `Continuous T`, not merely pointwise convergence.

The pinned Mathlib theorem
`tendsto_tprod_one_add_of_dominated_convergence` applies at any fixed
`z₀ : ℂ` with `f(z,k) = a_k z`, `g(k) = a_k z₀`, and filter `nhds z₀`.
The factor coefficient `a_k` is real and nonnegative. Choose the exact local
radius `R = ‖z₀‖ + 1`; eventually `‖z‖ ≤ R`, so for **every** `k`,

```text
‖a_k z‖ = a_k ‖z‖ ≤ R a_k.
```

The majorant `k ↦ R a_k` is summable. This follows by duplicating in the
new module the already reviewed argument used by the private
`cosineFactors_summable` in `CosineProduct.lean`: the pinned
`Real.summable_one_div_nat_add_rpow (1/2) 2` theorem and multiplication by
`1/π²`. The private lemma is not assumed accessible by name from a new
module. Termwise continuity gives `a_k z → a_k z₀`, and dominated
convergence yields `T(z) → T(z₀)`. The reasoning also applies when a factor
or the entire product is zero; it does not divide by a product.

Set `q(w) = -((π : ℂ) * w)^2` and
`D = {w : ℂ | Complex.sin ((π : ℂ) * w) ≠ 0}`. Pinned
`Complex.sin_eq_zero_iff`, together with `π ≠ 0`, identifies `Dᶜ` exactly
with the integer casts `{(k : ℂ) | k : ℤ}`. This set is countable, and
`Set.Countable.dense_compl ℂ` makes `D` dense in `ℂ`. An equivalent direct
proof of density is acceptable, but countability alone without the
no-isolated-points property is not.

At each `w ∈ D`, the frozen
`cosinePartialProduct_tendsto_waveSeries_of_sin_ne_zero w` and
`(cosineFactors_multipliable (q w)).hasProd.tendsto_prod_nat` are limits
of the **same** finite products. Hausdorff uniqueness of limits gives
`T(q w) = waveSeries (q w)`. The function `w ↦ T(q w)` is continuous by the
previous paragraph. The function `w ↦ waveSeries (q w)` is continuous
because the frozen `waveSeries_neg_pi_sq_eq_cos` identifies it pointwise
with `w ↦ Complex.cos (πw)`. Apply `Continuous.ext_on` to the dense set
`D`. This gives the equality for **every** `w`, including integers; no
pointwise-to-uniform inference is used.

Finally, `q` is surjective: for arbitrary `z : ℂ`, use
`IsAlgClosed.exists_pow_nat_eq (-z) (by norm_num : 0 < 2)` to choose
`y : ℂ` with `y² = -z`, then take `w = y / (π : ℂ)`; `π ≠ 0` gives
`q(w)=z`. The all-`w` identity therefore yields
`cosineFactor_tprod_eq_waveSeries z`. The second exported theorem follows
from the product equality and the existing `cosineFactors_multipliable z`
via `HasProd.tendsto_prod_nat`, unfolding `cosinePartialProduct`.

## Exact normalization and numerical ledger

For `z=q(w)`, each factor remains
`1 + a_k z = 1 - 4w²/(2k+1)²`. At `k=0` the factor is `1-4w²`.
For `N=0` the product is `1`; at `z=0`, the infinite product and
`waveSeries 0` are both `1`. The scalar in the surjectivity step is
`π`, rather than `2π`, because `q(w)=-π²w²`. The local majorant uses
`R=‖z₀‖+1`; its `1` is only an open-neighborhood margin and introduces
no new bound in the Padé theorem. The exact analytic coefficient remains
`1/(2j)!`, already encoded by `waveSeries`. There are no rounded constants.

This bridge proves an entire-function **value identity**. It does not yet
establish that the product's elementary symmetric coefficients equal
`1/(2j)!`: that transfer needs a justified expansion/interchange or
analytic coefficient uniqueness. It also supplies no Toeplitz,
Jacobi–Trudi, tableau-tail, normalized-pair existence, or all-order Padé
disk estimate. The frozen Target still quantifies over every `m ≥ 1`, every
reduced normalized pair, and every `z` in the closed disk of radius three.

No implementation, target modification, metadata change, or CI import
precedes independent approval of this exact contract. Implementation
must use the pinned Lean 4.33.1/Mathlib toolchain, kernel checks, and no
`sorry`, `admit`, `native_decide`, or added axioms.

## Source binding

SHA-256 at pre-review time:

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `docs/lean/proofs/MF-03/ALL_ORDER_SOURCE_OBLIGATIONS.md` | `96399593ee86dedb1020da3f9d9301e865c82eec1c801917edcf587e59a58aa6` |
| `lean-statements/NLA/Proofs/MF03/CosineProduct.lean` | `a80cd280636110b108e0a13702a55c57d15b739cfc1e73f73bd76eb330689c8a` |
| `lean-statements/NLA/Proofs/MF03/CosineDenseProduct.lean` | `0190869c463e7b06c1ced4beec8fdfd1b68481e60a688ff472b27a368e20be28` |
| Pinned Mathlib `Analysis/Normed/Ring/InfiniteProd.lean` | `58a90eef4bab4d6c8e13d5ab9732a45b196a3a6266b1c3b995af8b7158ff1101` |
| Pinned Mathlib `Topology/Algebra/Module/Cardinality.lean` | `f04f74d34af4d30ed28585376d54ae8a81bcfc4d31ae0576a89c4d437dd3d40e` |
| Pinned Mathlib `Analysis/SpecialFunctions/Trigonometric/Complex.lean` | `d26e466a4c8a3ea1031db34dce3c0ed4c7b6c0a9debc4d21cb6a6a65847d033c` |
| Pinned Mathlib `FieldTheory/IsAlgClosed/Basic.lean` | `87c1116c746be4329038b669ca67118a9e008472fb44ca4cc2ff9e7c6347e3f1` |
| Pinned Mathlib `Topology/Separation/Hausdorff.lean` | `4e6998adc898c3aac6d01e0c8bc916aa68794bf6cca0d3c57e43f76760151a87` |

Independent review should verify the exact all-complex statement, the
continuity majorant and `tprod` hypotheses, the integer-zero set and
density argument, the factor indexing and `π` scaling, and the stated
boundary before Lean work begins.
