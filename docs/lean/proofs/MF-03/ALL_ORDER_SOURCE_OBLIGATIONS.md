# MF-03 source-level obligations beyond the tail estimate

This note maps the authored proof of the `m ≥ 16` case to formal proof
obligations. It does not assert any new Lean theorem. The reviewed
`ALL_ORDER_TAIL_PRE_REVIEW.md` has its own fixed hash and is unchanged.

## Exact analytic chain in the manuscript

Let `tν = [π²(ν−1/2)²]⁻¹` for `ν ≥ 1`, and let
`F(z) = ∏_{ν≥1}(1+tν z) = ∑_{k≥0} e_k(t) z^k`.
For each `m ≥ 1`, the manuscript proves that the Padé denominator has

```text
Q_m(z) = ∑_{j=0}^m (-1)^j b_{m,j} z^j,
b_{m,j} = s_(m^m,j)(t) / s_(m^m)(t),
0 < b_{m,j} ≤ h_j(t_{m+1},t_{m+2},...) ≤ S_m^j,
S_m = ∑_{ν>m} tν.
```

The `j=0` term is `1`. This is an **exact coefficient statement** about the
normalized denominator; a bound for an arbitrary polynomial with the Padé
equations would need uniqueness to identify its coefficients. The Toeplitz
system for unknown coefficients has entries `e_(m+i−j)` for `1 ≤ i,j ≤ m`.
The determinant is `s_(m^m)(t)>0`; Cramer's rule and the dual Jacobi–Trudi
identity give the quotient above. Its denominator is positive because the
tableau filled with row number `r` in row `r` has positive weight. In each
tableau of shape `(m^m,j)`, all entries in the extra bottom row are at least
`m+1`, so restriction to the rectangle bounds the numerator by the rectangle
sum times `h_j(tail)`. The final `h_j ≤ S_m^j` follows by comparing weakly
increasing tuples with all ordered tuples.

With `R=3`, put `B = ∑_{j=0}^m b_{m,j}3^j`. The coefficient estimate and
`3S_m < 1/2` give `B ≤ 1/(1−3S_m)<2`, hence
`|Q_m(z)| ≥ 2−B>0` for `|z|≤3`. Since the numerator truncates `Q_mF`,
`|P_m(z)−Q_m(z)| ≤ B(F(3)−1)`. Consequently
`|P_m/Q_m−1| ≤ (F(3)−1)/(1−6S_m)`. The strict `m ≥ 16` conclusion also
uses `F(3) ≤ 6179/2120` and `6S_m <1/24`.

## Cosine product bridge

Pinned Mathlib has `Complex.tendsto_euler_sin_prod` in
`Mathlib/Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean`:
the finite Euler sine products tend to `sin(πw)`. It does not appear to
contain a directly named odd-factor product for `cos(πw)` or the `cosh√z`
product. A derivation would combine `sin(2πw)=2sin(πw)cos(πw)` with even/odd
factor splitting. Away from zeros of `sin(πw)`, divide and cancel the even
factors; then extend to excluded values using continuity or an analytic
identity. For arbitrary complex `z`, set `w²=−z/π²`; the odd factors become
`1+z/[π²(ν−1/2)²]`. Independently, prove the power-series identity
`cos(πw)=∑_{k≥0}(-1)^k(πw)^(2k)/(2k)!` to identify the coefficients with
`1/(2k)!`. This branch-free formulation avoids making a square-root choice
in the target.

Formal output needed: a theorem identifying every coefficient of the
convergent product with `1/(2k)!`, or an equivalent entire-function equality
strong enough to derive those coefficients. A pointwise product identity
alone is insufficient unless the coefficient transfer is proved.

## Schur/tableau formalization gap

The pinned Mathlib tree contains
`Mathlib/Combinatorics/Young/SemistandardTableau.lean`, including tableau
rows and columns, `row_weak`, `col_strict`, and `highestWeight`. Source search
found no Schur symmetric-function or Jacobi–Trudi module. Consequently the
following cannot be treated as available lemmas without further proof:

1. Definitions and summability of tableau weights in infinitely many
   positive variables, with the weight sum bounded by `(∑ν tν)^L` for a
   fixed shape of size `L`.
2. Dual Jacobi–Trudi for the relevant Toeplitz minors, including the exact
   partition transposition and Cramer sign `(-1)^j`.
3. The restriction map from shape `(m^m,j)` to `(m^m)` and the bound on
   the extra bottom row. This must preserve the exact index `ν ≥ m+1`.
4. Positivity of `s_(m^m)(t)` and `s_(m^m,j)(t)`, invertibility of the Padé
   coefficient matrix, and the resulting normalized pair with degree `≤m`.
5. Passing finite-variable identities to the infinite positive sequence.
   Positivity and the finite total sum control the limits, but the limit
   argument must be explicit.

An alternative denominator coefficient proof is possible, but it must
establish the same actual bound for the frozen Padé equations. The existing
`Reduction.lean` and `Transport.lean` can handle reduced representatives
after a concrete normalized pair and its disk bound are available; they do
not supply these analytic coefficient facts.

## Source binding

| Source | SHA-256 |
| --- | --- |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `references/colbrook-matrix-functions-2026-09-11/results/wave_kernel_finite_certificate.json` | `6d000c2b0b37acac1fca07bac239534d68177213da56f9c34aa5a5105c9cbaa8` |
| `references/colbrook-matrix-functions-2026-09-11/code/wave_kernel_certificate.py` | `73587f8a4a5afd12bd6f33ae9ffb5b85c9388831cf152b48a4c64595f84c3155` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |

The finite certificate covers only `1 ≤ m ≤ 15`; it does not replace any
of the infinite-variable or product obligations above.
