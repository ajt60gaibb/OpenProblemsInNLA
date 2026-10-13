# MF-03 all-order analytic tail: pre-proof review

## Frozen target and exact proposed first lemma

The frozen `NLA.Statements.MF03.Target` asks for existence of a reduced
normalized Padé pair and the closed-disk bound for **every** positive order.
The finite-range theorem already covers `1 ≤ m ≤ 15`. The proposed first
analytic module, `lean-statements/NLA/Proofs/MF03/CosineTail.lean`, would
establish only the exact numerical tail estimate used by the authored proof.
In namespace `NLA.Proofs.MF03`, its public definitions and theorem would be:

```lean
def cosineFactor (ν : ℕ) : ℝ :=
  1 / (Real.pi ^ 2 * ((ν : ℝ) - 1 / 2) ^ 2)

def cosineTail (m : ℕ) : ℝ :=
  ∑' k : ℕ, cosineFactor (m + k + 1)

theorem cosineTail_lt_one_div_nine_mul
    (m : ℕ) (hm : 1 ≤ m) :
    cosineTail m < 1 / (9 * (m : ℝ))
```

Here `k = 0` means `ν = m + 1`, so `cosineTail m` is exactly the manuscript's
`S_m = ∑_{ν>m} [π²(ν−1/2)²]⁻¹`, with no missing or duplicated endpoint.
The theorem is valid for all positive `m`; using it at `m ≥ 16` is a later
specialization. The companion arithmetic corollary required by the manuscript
is `16 ≤ m → 6 * cosineTail m < 1 / 24`, since
`6/(9m) ≤ 6/(9·16) = 1/24`.

## Exact mathematical proof

For `n = m+k ≥ 1`, put `x = n + 1/2`. The identity

```text
x² = n(n+1) + 1/4 > n(n+1) > 0
```

gives

```text
0 < 1/x² < 1/[n(n+1)] = 1/n − 1/(n+1).
```

For every `N`, the comparison sum telescopes exactly:

```text
∑_{k=0}^{N−1} 1/[(m+k)(m+k+1)] = 1/m − 1/(m+N).
```

Its limit is `1/m`. Comparison proves summability of the positive cosine
summands and `cosineTail m ≤ 1/(π²m)`. Mathlib's `Real.pi_gt_three`
gives `π² > 9`; as `m > 0`, `1/(π²m) < 1/(9m)`. This proof is pointwise,
telescoping, and exact. It avoids the midpoint integral in the manuscript
while proving the same displayed bound, with the same index and strictness.

The pinned Mathlib tree contains `Real.pi_gt_three` in
`Mathlib/Analysis/Real/Pi/Bounds.lean`; `Summable.tsum_le_tsum` and the
`summable_nat_add_iff`/real p-series tools are available for the infinite-sum
step. The finite telescoping identity can instead be proved by induction,
then passed to the limit. These names are feasibility leads, not assertions
that a Lean proof has already typechecked.

## Numerical threshold and the separate `f(3)` obligation

The authored proof bounds

```text
f(3) = ∑_{j=0}∞ 3^j/(2j)! ≤
  1 + 3/2 + 3/8 + (3/80)/(1−3/56)
  = 6179/2120 < 35/12.
```

The `j=3` term is `3/80`; for `j ≥ 3`, the next-term ratio is
`3/[(2j+2)(2j+1)] ≤ 3/56`. This is an independent future Lean lemma,
not an assumption of `cosineTail_lt_one_div_nine_mul`. Together with
`6S_m < 1/24`, it gives the strict rational margin

```text
(f(3)−1)/(1−6S_m)
  < [(6179/2120)−1]/(1−1/24)
  = 12177/6095 = 2−13/6095 < 2.
```

For orientation only, a direct finite-sum calculation with an integral
remainder enclosure gave `S_16` approximately `0.00633051540`, versus
`1/144 ≈ 0.00694444444`, and `6S_16 ≈ 0.0379830924`, versus
`1/24 ≈ 0.0416666667`. The exact inequalities above carry the proof; these
floating-point figures are not certificates.

## Remaining all-order obligations

This tail lemma alone does **not** prove the frozen target. Later proofs
must connect the cosine product to the coefficient series
`1/(2j)!`, establish existence and uniqueness of the normalized Padé pair,
and prove the manuscript's Schur/tableau denominator estimate
`0 < b_{m,j} ≤ S_m^j` for `1 ≤ j ≤ m`. The closed-disk estimate must then
be transported to every reduced representation, including pole freedom.
The pinned Mathlib source search found an Euler sine product module, but no
ready theorem spelling out this cosine/hyperbolic-cosine product; that bridge
should be treated as a real implementation obligation. No existing proof,
statement, metadata, or CI module is to be modified for this first lemma.

## Source binding

SHA-256 at pre-review time:

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.pdf` | `344fa669207764375a47432d47782b52ccee3c0f3c99326541039361ebb50726` |
| `references/colbrook-matrix-functions-2026-09-11/verification/reviews/MF-03-review.md` | `cccbb11ca9e42a0f27e72d3b351f76c66b5a06eee69f7c6e367ebab8e0c79423` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/NLA/Proofs/MF03/FiniteRange.lean` | `b83eadb2aa7bb33dfaf8f553be0ae16df5cab60762a90ff11cea2e609f38278a` |

The manuscript's relevant equations are `(product)`, `(sm)`, `(coshbound)`,
and the `m ≥ 16` paragraph in Theorem 1's proof. Independent review of this
contract is required before implementing its Lean module.
