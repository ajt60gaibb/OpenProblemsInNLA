# MF-03 exact finite rectangular determinant/tableau identity

**Status:** source-locked mathematical precontract for independent review before implementation. This is the `j=0` specialization of the independently audited original finite augmented determinant/tableau identity, with an explicit proof that the `j=0` augmented Young diagram and weight are the original rectangle.

For all `N,m : ℕ`, including zero and empty tableau domains, prove the exact original identity

```text
finiteCosineRectDet N m = finiteRectTableauSum N m.
```

`finiteCosineRectDet N m` is the determinant of the original finite elementary-coefficient matrix `(m+c−r)` from `FiniteDeterminantLimit.lean`. `finiteRectTableauSum N m` is the original sum of `finiteRectWeight m` over bounded semistandard tableaux on `finiteRectShape m` from `FiniteTableauTail.lean`. The right side must not be replaced with an auxiliary path sum or a new weight.

The source defines `finiteCosineAugDet N m 0 = finiteCosineRectDet N m`; its augmented tableau shape at `j=0` has no bottom cells, hence is exactly `finiteRectShape m` as a `YoungDiagram`, and `finiteBottomWeight 0 m T = 1`. Thus the audited `finiteCosineAugDet_eq_augTableauSum N m 0 (Nat.zero_le m)` yields the displayed identity with coefficient one. The proof requires neither positivity nor a nonzero denominator. It must preserve the rectangle's `m×m` cells and the factors `cosineFactor(T(r,c)+1)`.

Proposed exact Lean signature in a separate module:

```lean
theorem finiteCosineRectDet_eq_rectTableauSum (N m : ℕ) :
    finiteCosineRectDet N m = finiteRectTableauSum N m := by
  ...
```

After independent approval, implement and separately audit the imported exact signature with LeanCert kernel, including `N=0` and `m=0`. This identity will permit the finite coefficient-one augmented-determinant tail bound to be stated against the original rectangular determinant, then passed to the infinite determinant limits. The infinite claim and full Padé target remain separate obligations.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/NLA/Proofs/MF03/FiniteDeterminantLimit.lean` | `dae4fe36fa8483141b5b96e76f4a7dc58a30f2d508bb405ea58ef015413577d7` |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauTail.lean` | `245226b8e05f0aaa15d41a491ec74825a624db02a68a68e6f0741321ef49307d` |
| `lean-statements/NLA/Proofs/MF03/FiniteAugDetTableau.lean` | `0f39a4f2d091ceee4b3e2f9b3a90aa9217d5bf530202dbb65952f91d1dc60466` |
