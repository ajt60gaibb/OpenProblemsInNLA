# MF-03 value at three and large-order arithmetic: pre-proof contract

## Exact proposed Lean interface

The proposed new module is
`lean-statements/NLA/Proofs/MF03/WaveAtThree.lean`, importing the independently
reviewed `NLA.Proofs.MF03.CosineTail`. In namespace `NLA.Proofs.MF03`:

```lean
noncomputable def waveAtThree : ℝ :=
  ∑' j : ℕ, (3 : ℝ) ^ j / (((2 * j).factorial : ℕ) : ℝ)

theorem waveAtThree_le_rational :
    waveAtThree ≤ (6179 : ℝ) / 2120

theorem largeOrder_numeric_margin
    (m : ℕ) (hm : 16 ≤ m) :
    (waveAtThree - 1) / (1 - 6 * cosineTail m) ≤
      (2 : ℝ) - 13 / 6095
```

The first definition is the manuscript's real value
`f(3)=∑_{j≥0}3^j/(2j)!`; it is not a redefinition of the frozen complex
Padé target. The last statement records a fixed positive margin below `2`
for every order `m ≥ 16`. In particular it implies the manuscript's strict
numeric bound. It contains the actual `cosineTail m`, not an unconstrained
stand-in. Its denominator is proved positive in the proof; no positivity
hypothesis is silently assumed.

## Exact series estimate

Write `a_j=3^j/(2j)!`. The first three terms are

```text
a_0 = 1,       a_1 = 3/2,       a_2 = 3/8,
a_3 = 27/720 = 3/80.
```

For every `j ≥ 3`, the factorial recurrence gives

```text
a_(j+1) / a_j = 3 / [(2j+2)(2j+1)] ≤ 3/56.
```

The denominator is at least `8·7=56`, and all `a_j` are nonnegative.
Induction yields `a_(3+k) ≤ (3/80)(3/56)^k`. The geometric tail therefore
satisfies

```text
∑_{j=3}∞ a_j ≤ (3/80) / (1−3/56) = 21/530.
```

The first three terms total `23/8`; hence

```text
waveAtThree ≤ 23/8 + 21/530 = 6179/2120 < 35/12.
```

This is the manuscript's `(coshbound)` estimate exactly. No decimal
approximation or truncated-series guess enters the proof. For Lean,
`Real.cosh_eq_tsum` at `√3` and `(√3)²=3` can provide summability of the
series; alternatively the geometric domination of its tail gives
summability directly. Either route must prove the split at `j=3`, the
factorial ratio, and the infinite geometric sum, rather than treating
`tsum` as automatically equal to a limit.

## Exact margin from the reviewed cosine tail theorem

For `m ≥ 16`, `cosineTail_lt_one_div_nine_mul m` implies

```text
6*cosineTail m < 6/(9m) ≤ 1/24,
1−6*cosineTail m > 23/24 > 0.
```

The value bound gives `waveAtThree−1 ≤ 4059/2120`. The rational identity

```text
(12177/6095)·(23/24) = 4059/2120
```

then yields, by multiplying the positive denominator bound,

```text
(waveAtThree−1)/(1−6*cosineTail m)
   ≤ 12177/6095 = 2−13/6095 < 2.
```

The first inequality remains valid even without a separately proved lower
bound on `waveAtThree−1`: compare its upper bound with the positive multiple
of the denominator, then divide by that denominator. This avoids an
unnecessary monotonicity premise. The rational margin `13/6095` is exact.

## Boundary and missing obligations

This module would prove only a numerical component of the `m ≥ 16` argument.
It would not establish that `waveAtThree` equals the value at `3` of the
infinite product with factors `cosineFactor ν`, or that the product's
coefficients are `1/(2j)!`; the cosine-product bridge remains open. The
Schur/tableau denominator coefficient theorem, normalized Padé existence,
and the disk estimate also remain open. The current finite-range theorem
covers `1 ≤ m ≤ 15`; this numerical lemma does not change the frozen target,
the canonical problem identity, or those finite certificates. The rational
margin must not be presented as a proof of `NLA.Statements.MF03.Target`.

No implementation, existing proof module, metadata, or CI file is to be
changed before independent review of this contract.

## Source binding

SHA-256 at contract time:

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `references/colbrook-matrix-functions-2026-09-11/results/wave_kernel_finite_certificate.json` | `6d000c2b0b37acac1fca07bac239534d68177213da56f9c34aa5a5105c9cbaa8` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/NLA/Proofs/MF03/FiniteRange.lean` | `b83eadb2aa7bb33dfaf8f553be0ae16df5cab60762a90ff11cea2e609f38278a` |
| `lean-statements/NLA/Proofs/MF03/CosineTail.lean` | `41fc5b7da2f1033b17608a56507aeeba555099f933a1b5eea05477331e8ace8b` |

The manuscript's relevant source lines are `(coshbound)` and the `m ≥ 16`
paragraph in the proof of Theorem 1. The proposed theorem names and
signatures are fixed for the independent pre-proof review.
