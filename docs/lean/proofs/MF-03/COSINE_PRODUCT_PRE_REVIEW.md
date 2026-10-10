# MF-03 cosine product: pre-proof contract

## Frozen target and proposed Lean interface

The canonical target is the unchanged
`NLA.Statements.MF03.Target`: normalized Padé coefficient equations for the
entire series with coefficients `1/(2j)!`, followed by a disk bound for every
reduced pair. The manuscript's product formula must identify **that same
series** with the positive-factor cosine product for every complex `z`.

In a new `lean-statements/NLA/Proofs/MF03/CosineProduct.lean` module, importing
the reviewed `CosineTail` and `WaveAtThree` modules, propose these public
declarations in namespace `NLA.Proofs.MF03`:

```lean
noncomputable def waveSeries (z : ℂ) : ℂ :=
  ∑' j : ℕ, z ^ j / (((2 * j).factorial : ℕ) : ℂ)

noncomputable def cosinePartialProduct (N : ℕ) (z : ℂ) : ℂ :=
  ∏ k ∈ Finset.range N, (1 : ℂ) + (cosineFactor (k + 1) : ℂ) * z

theorem cosineFactors_multipliable (z : ℂ) :
    Multipliable (fun k : ℕ =>
      (1 : ℂ) + (cosineFactor (k + 1) : ℂ) * z)

theorem cosinePartialProduct_tendsto_waveSeries (z : ℂ) :
    Filter.Tendsto (fun N : ℕ => cosinePartialProduct N z)
      Filter.atTop (nhds (waveSeries z))

theorem waveSeries_eq_cosineProduct (z : ℂ) :
    waveSeries z =
      ∏' k : ℕ, (1 : ℂ) + (cosineFactor (k + 1) : ℂ) * z

theorem waveSeries_zero : waveSeries 0 = 1

theorem waveSeries_three_eq_waveAtThree :
    waveSeries (3 : ℂ) = (waveAtThree : ℂ)
```

The convergence theorem prevents the `tprod` equality from relying on the
fallback value used when a product is not multipliable. The final theorem
connects the product's value at the radius `3` to the independently proved
real bound `waveAtThree ≤ 6179/2120`. It does not itself assert a disk or
Padé denominator bound.

## Indexing, normalization, and signs

`cosineFactor ν = [π²(ν−1/2)²]⁻¹` is already fixed in `CosineTail.lean`.
The factor with `k=0` in the proposed finite product is `ν=1`, namely
`1+4z/π²`; there is no factor at `ν=0`. At `N=0`, the finite product is the
empty product `1`. At `z=0`, every factor is `1`, and the series has just its
`j=0` term `1`, proving the normalization claimed above.

The source's Euler product is

```text
∑_{j=0}∞ z^j/(2j)!
  = ∏_{ν=1}∞ (1 + z/[π²(ν−1/2)²]).
```

Every factor has a **plus** sign. Its finite-product coefficients are
nonnegative real elementary symmetric sums in the positive factors; the
series coefficients are `+1/(2j)!`. These coefficients are distinct from
the alternating coefficients `(-1)^j b_(m,j)` of the eventual Padé
denominator. The product result must not be used to identify the latter
without the separate Schur/tableau argument.

## Exact mathematical proof route

1. **Convergence.** The factor sequence satisfies
   `∑_{k≥0} cosineFactor(k+1)<∞`: it is a positive constant multiple of
   the shifted p-series `∑_{k≥0}(k+1/2)⁻²`. For each complex `z`, the
   perturbations `(cosineFactor(k+1):ℂ)*z` are absolutely summable.
   Mathlib's generic `multipliable_one_add_of_summable` proves the pointwise
   infinite product exists. On every compact set of `w` values, the odd
   sine-product perturbations `−4w²/(2k+1)²` have a common summable norm
   majorant. The pinned `Summable.hasProdUniformlyOn_nat_one_add` or
   `Summable.hasProdLocallyUniformlyOn_nat_one_add` supports uniform
   convergence there, giving a continuous odd-factor product.

2. **Even/odd splitting.** Put

   ```text
   S_N(w) = ∏_{n=1}^N (1−w²/n²),
   C_N(w) = ∏_{k=0}^{N−1} (1−4w²/(2k+1)²).
   ```

   Reindexing a finite product proves the exact identity
   `S_(2N)(2w)=S_N(w) C_N(w)`. Pinned Mathlib supplies
   `Complex.tendsto_euler_sin_prod`, namely
   `πw S_N(w) → sin(πw)`. Applied also to `2w` along `2N`, this and
   `sin(2πw)=2sin(πw)cos(πw)` imply `C_N(w)→cos(πw)` whenever
   `w∉ℤ`. At such `w`, `sin(πw)≠0`, so division is justified. At `w=0`,
   `C_N(0)=1=cos 0` directly. At the other integers, the sine quotient is
   `0/0`; extend from nearby nonintegers using continuity of the locally
   uniform product and of `cos`. This exceptional-set step is mandatory.

3. **Substitution and series.** For arbitrary `z∈ℂ`, choose `w∈ℂ` with
   `(πw)²=−z`. Then each odd factor becomes

   ```text
   1−4w²/(2k+1)²
      = 1+z/[π²(k+1/2)²]
      = 1+(cosineFactor(k+1):ℂ) z.
   ```

   Pinned `Complex.cos_eq_tsum` gives
   `cos(πw)=∑_j (-1)^j(πw)^(2j)/(2j)!`.
   Since `(πw)²=−z`, its numerator is
   `(-1)^j(−z)^j=z^j`, term by term. This proves the proposed
   `cosinePartialProduct_tendsto_waveSeries` and `tprod` identity for
   every complex `z`, including zero and the values corresponding to
   integer `w`. The choice of square root affects `w` by a sign but not
   either side; the theorem itself remains branch free.

4. **Value at three.** The real and complex `tsum` coefficients agree under
   the canonical real-to-complex cast. Therefore `waveSeries (3:ℂ)` equals
   `(waveAtThree:ℂ)` exactly, with no numerical approximation.

The wave series is summable for every `z`, by the cosine-series theorem
after the square substitution or by factorial growth. Both infinite sums
and the product limit must be justified in Lean; a formal manipulation of
an unproved `tsum` is insufficient.

## What this module would still leave open

For the Schur proof, finite products must be expanded as elementary
symmetric polynomials, and their fixed-degree coefficients must be shown
to converge to `1/(2j)!` as `N→∞`. The complex function identity above
provides the analytic source, but the coefficient extraction/interchange
must be proved before the manuscript's Toeplitz matrix may be populated
with the frozen `1/(2j)!` coefficients. That bridge may be part of a later
Schur module or a separately reviewed coefficient lemma; it is not silently
included in the proposed theorems.

The determinant/dual Jacobi–Trudi identity, strict positivity,
`0<b_(m,j)≤S_m^j`, normalized Padé existence and uniqueness, and the
closed-disk estimate for all reduced pairs remain separate obligations.
Neither the existing finite-range theorem nor the numerical tail/value
lemmas establish them. No frozen statement, existing proof module,
metadata, or CI file is to be changed for this product module.

## Source binding

SHA-256 at pre-review time:

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.pdf` | `344fa669207764375a47432d47782b52ccee3c0f3c99326541039361ebb50726` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/NLA/Proofs/MF03/CosineTail.lean` | `41fc5b7da2f1033b17608a56507aeeba555099f933a1b5eea05477331e8ace8b` |
| `lean-statements/NLA/Proofs/MF03/WaveAtThree.lean` | `824320b42ef6c052c12f6e68ebfb774a4ed969544a70f32a47cd0d8102682b6a` |
| Pinned Mathlib `Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean` | `0988322f130952835b0da8d43d24b44c281af10bf149bb869ac750160ec1d5ac` |
| Pinned Mathlib `Analysis/SpecialFunctions/Trigonometric/Series.lean` | `307b22a20bcee20728e6bfda013c6f08fb126a25a2fe5e7d6cedb031bcd6a079` |

The mathematical source is the manuscript's equation `(product)` and its
preceding definition of `f`. Independent mathematical and Lean review of
this contract is required before implementation.
