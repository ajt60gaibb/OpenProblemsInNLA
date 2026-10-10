# MF-03 exact nonnegative original determinant ratio and coefficient-one tail

**Status:** source-locked exact mathematical and numerical precontract for independent review before Lean implementation. This is an original determinant ratio, not yet a Padé coefficient identity or disk bound.

For every `m,j : ℕ` with `j≤m`, retain the original determinants `cosineAugDet m j` and `cosineRectDet m` from `FiniteDeterminantLimit.lean` and the original zero-based factor tail `cosineTail m = Σ' t:ℕ, cosineFactor(m+t+1)`. The independently audited coefficient-one inequality is

```text
cosineAugDet m j ≤ cosineRectDet m * (cosineTail m)^j.
```

The separately reviewed positivity gate proves `0 < cosineRectDet m`, so division by that **actual** rectangular determinant gives exactly

```text
cosineAugDet m j / cosineRectDet m ≤ (cosineTail m)^j.
```

No numerical coefficient or exponent changes. The denominator is never replaced with a tableau normalization or lower estimate. For the lower sign, the exact finite augmented determinant/tableau identity and kernel-proved `finiteAugTableauSum_pos N m j hj (m<N)` imply `0≤finiteCosineAugDet N m j` eventually in `N`; fixed-size determinant convergence then gives `0≤cosineAugDet m j`. Dividing by the positive original rectangular determinant yields

```text
0 ≤ cosineAugDet m j / cosineRectDet m.
```

Both inequalities include `m=0,j=0` (ratio `1`), `j=0`, `j=m`, ties in tableau entries where allowed, and all positive orders. No finite enumeration, approximation, nonzero assumption on the augmented determinant, or use of a ratio before proving the denominator positive is permitted.

Suggested exact public Lean declaration in a separate module:

```lean
theorem cosineAugDet_ratio_bounds (m j : ℕ) (hj : j ≤ m) :
    0 ≤ cosineAugDet m j / cosineRectDet m ∧
      cosineAugDet m j / cosineRectDet m ≤ (cosineTail m)^j := by
  ...
```

If an intermediate public theorem `0≤cosineAugDet m j` is used, freeze and audit its exact signature. This ratio is a precise source coefficient bound; the later Cramer/Padé coefficient identity and the full all-order disk Target remain open and require their own reviewed gates.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/NLA/Proofs/MF03/FiniteDeterminantLimit.lean` | `dae4fe36fa8483141b5b96e76f4a7dc58a30f2d508bb405ea58ef015413577d7` |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauCanonical.lean` | `0049d1f97e3e5d25962cafd667ca4e35137aa8ef6239bf08a9730ddc59aa33cb` |
| `lean-statements/NLA/Proofs/MF03/FiniteAugDetTableau.lean` | `0f39a4f2d091ceee4b3e2f9b3a90aa9217d5bf530202dbb65952f91d1dc60466` |
| `lean-statements/NLA/Proofs/MF03/OriginalDeterminantInfiniteTail.lean` | `bd90c1e22cc06a20d7fb94572db30bab46d79fb3a89e5ef282dfc3416c332896` |
| `lean-statements/NLA/Proofs/MF03/RectDeterminantPositivity.lean` | `3b4e0239c569aebf3ac55e71100b7f455d686243a5ea7541b04e4a80dc249ceb` |

The positivity source remains a directly checked draft until its independent imported audit and aggregate import. This contract does not treat it as already audited.
