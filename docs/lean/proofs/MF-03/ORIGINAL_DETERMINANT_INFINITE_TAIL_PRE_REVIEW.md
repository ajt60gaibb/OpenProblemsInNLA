# MF-03 coefficient-one tail inequality for the original determinants

**Status:** source-locked exact mathematical and numerical precontract for independent review before Lean implementation. The full Padé disk target and denominator positivity remain separate obligations.

## Exact objects and inequalities

`finiteCosineAugDet N m j`, `finiteCosineRectDet N m`, `cosineAugDet m j`, and `cosineRectDet m` are exactly the original elementary-coefficient determinants from `FiniteDeterminantLimit.lean`. The exact infinite factor tail is `cosineTail m = Σ' t:ℕ, cosineFactor(m+t+1)`; it starts at zero-based factor label `k=m`. Retain the original `cosineFactor(k+1)`, no shift to `m+1` labels or replacement by a new weight.

For every `N,m,j : ℕ` with `j≤m`, prove

```text
finiteCosineAugDet N m j
  ≤ finiteCosineRectDet N m * (cosineTail m)^j.
```

This is the already kernel-proved `finiteAugTableauSum_le_rect_mul_cosineTail`, transported through the independently audited exact augmented determinant/tableau equality and the separately reviewed exact rectangular determinant/tableau equality. The bound has coefficient one and exponent the actual bottom-row length `j`; it remains valid for `N=0`, `m=0`, `j=0`, and `j=m` without division or nonzero assumptions.

For every `m,j : ℕ` with `j≤m`, pass the previous inequality through the already kernel-proved fixed-size determinant limits to obtain the original infinite determinant bound

```text
cosineAugDet m j ≤ cosineRectDet m * (cosineTail m)^j.
```

Use `finiteCosineAugDet_tendsto m j hj`, `finiteCosineRectDet_tendsto m`, continuity of multiplication by the fixed real `(cosineTail m)^j`, and order closedness. No numerical approximation or finite-order enumeration is involved. The infinite inequality has no absolute value or ratio; positivity of `cosineRectDet m` and the later coefficient ratio require separate proofs. Both statements preserve the source's coefficient-one bound.

## Proposed exact Lean signatures

```lean
theorem finiteCosineAugDet_le_rectDet_mul_cosineTail
    (N m j : ℕ) (hj : j ≤ m) :
    finiteCosineAugDet N m j ≤
      finiteCosineRectDet N m * (cosineTail m)^j := by
  ...

theorem cosineAugDet_le_rectDet_mul_cosineTail
    (m j : ℕ) (hj : j ≤ m) :
    cosineAugDet m j ≤ cosineRectDet m * (cosineTail m)^j := by
  ...
```

Independently verify the original determinant definitions, exact tail start/factor, all fixed-size limit hypotheses, multiplication continuity and inequality direction, before implementing or importing either theorem. Imported exact-signature/source/axiom audits must use LeanCert kernel.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/NLA/Proofs/MF03/FiniteDeterminantLimit.lean` | `dae4fe36fa8483141b5b96e76f4a7dc58a30f2d508bb405ea58ef015413577d7` |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauInfiniteTail.lean` | `55e0d3d4c9243e984019d930d8ae1111899b4a3e77b6a1f434449ae3150c9f8a` |
| `lean-statements/NLA/Proofs/MF03/FiniteAugDetTableau.lean` | `0f39a4f2d091ceee4b3e2f9b3a90aa9217d5bf530202dbb65952f91d1dc60466` |
| `lean-statements/NLA/Proofs/MF03/FiniteRectDetTableau.lean` | `e6e11ca2b94ad996a90e295e854d0eaee211b2c7c17c832f70db4caadab91114` |

The latter rectangular source remains a direct-checked draft until its independent imported audit and aggregate import. No inference in this contract treats a draft as already audited.
