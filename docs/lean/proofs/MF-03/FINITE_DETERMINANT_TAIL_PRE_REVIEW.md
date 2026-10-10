# MF-03 original finite determinant tail: exact next numerical gate

**Status:** source-locked mathematical and numerical precontract for independent review before Lean implementation. It follows the exact finite determinant/tableau equality and the already kernel-proved augmented-tableau tail inequality. It does not claim the infinite determinant ratio or the full Padé disk target.

## Original objects and exact claim

For arbitrary `N,m,j : ℕ` with `hj : j ≤ m`, retain the original `finiteCosineAugDet N m j` from `FiniteDeterminantLimit.lean`, the original `finiteRectTableauSum N m` and `finiteAugTableauSum N m j` from `FiniteTableauTail.lean`, and the original `finiteCosineTail N m = Σ_{k:Fin N, m≤k} cosineFactor(k+1)` from `FiniteTableauTailBound.lean`. The finite augmented determinant/tableau equality is the immediately preceding independently reviewed gate. The exact desired bound is

```text
finiteCosineAugDet N m j
  ≤ finiteRectTableauSum N m * (finiteCosineTail N m)^j.
```

This is the **original determinant**, not a newly defined path or tableau determinant. It is exactly the existing tableau bound transported through the proved determinant equality, with coefficient one, exponent `j`, and zero-based tail beginning at `k=m`. No absolute value, ratio, sign replacement, or finite-order enumeration is inserted. The source's `cosineFactor(k+1)` and actual `j` bottom cells are unchanged. The result covers `m=0`, `j=0`, `j=m`, and `N=0`; no nonzero denominator is required.

Suggested exact Lean declaration, in a separate `FiniteDeterminantTail` module:

```lean
theorem finiteCosineAugDet_le_rect_mul_tail
    (N m j : ℕ) (hj : j ≤ m) :
    finiteCosineAugDet N m j ≤
      finiteRectTableauSum N m * (finiteCosineTail N m) ^ j := by
  ...
```

The proof must compose `finiteCosineAugDet_eq_augTableauSum N m j hj` with the already kernel-proved `finiteAugTableauSum_le_rect_mul_tail N m j hj`, without strengthening assumptions or weakening the numerical coefficient. Review the exact imported theorem signatures and dependency trust independently before import.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/NLA/Proofs/MF03/FiniteDeterminantLimit.lean` | `dae4fe36fa8483141b5b96e76f4a7dc58a30f2d508bb405ea58ef015413577d7` |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauTailBound.lean` | `957fc6c69e5c778900a49fdae04d61f9a99dd5ef28fdadd48b75a2b01749a2a3` |
| `lean-statements/NLA/Proofs/MF03/FiniteAugDetTableau.lean` | `0f39a4f2d091ceee4b3e2f9b3a90aa9217d5bf530202dbb65952f91d1dc60466` |

Later gates must separately identify the original finite rectangular determinant with `finiteRectTableauSum`, transport the finite bound to the infinite determinant limit, establish denominator positivity, and prove the exact Padé disk target. This precontract makes no claim about those stages.
