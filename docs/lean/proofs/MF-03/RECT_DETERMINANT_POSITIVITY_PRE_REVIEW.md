# MF-03 uniform positive lower bound for the original rectangular determinant

**Status:** exact mathematical and numerical precontract for independent review before Lean implementation. The aim is positivity of the original infinite rectangular elementary-coefficient determinant, needed before forming any coefficient ratio. Positivity of each finite determinant alone does not justify positivity of its limit; this contract fixes one positive lower bound independent of the cutoff `N`.

## Exact lower bound and original object

For each `m : ℕ`, define the real number

```text
canonicalRectWeight m
  = ∏ r∈range m, ∏ c∈range m, cosineFactor(r+1).
```

It is exactly the original `finiteRectWeight m` of the already kernel-proved `canonicalRectTableau N m (m≤N)`, whose cell `(r,c)` has zero-based label `r`. Each factor is positive for every `r`, so `canonicalRectWeight m > 0`, including `m=0` where the empty product is `1`.

For all `N,m` with `m≤N`, the original finite rectangular determinant satisfies the **uniform** inequality

```text
canonicalRectWeight m ≤ finiteCosineRectDet N m.
```

The independently audited `finiteCosineRectDet_eq_rectTableauSum` identifies the determinant with the original weighted sum over bounded rectangular tableaux. The canonical tableau is a member of that sum and has exactly the displayed fixed weight; every other summand is nonnegative because each original factor `cosineFactor(T(r,c)+1)` is positive. No division or finite enumeration is used.

The existing kernel-proved `finiteCosineRectDet_tendsto m` then yields

```text
canonicalRectWeight m ≤ cosineRectDet m,
0 < cosineRectDet m.
```

The sequence bound is eventual because `m≤N` for all sufficiently large `N`. Passing it through the limit uses order closedness; the fixed positive lower bound proves the strict final inequality. This covers `m=0` and every positive order, with no unproved monotonicity assumption for determinants.

## Proposed exact Lean declarations

Use a separate `RectDeterminantPositivity` module with these public facts, or a direct equivalent that preserves the same fixed canonical product:

```lean
noncomputable def canonicalRectWeight (m : ℕ) : ℝ :=
  ∏ r ∈ Finset.range m, ∏ c ∈ Finset.range m, cosineFactor (r + 1)

theorem canonicalRectWeight_pos (m : ℕ) :
    0 < canonicalRectWeight m := by
  ...

theorem canonicalRectWeight_le_finiteRectDet
    (N m : ℕ) (hm : m ≤ N) :
    canonicalRectWeight m ≤ finiteCosineRectDet N m := by
  ...

theorem cosineRectDet_pos (m : ℕ) :
    0 < cosineRectDet m := by
  ...
```

The public strict positivity theorem must not assume the desired nonzero denominator. If the canonical tableau's exact weight or the uniform bound requires helper lemmas, freeze and independently audit their exact signatures as well. Each imported theorem must pass LeanCert kernel with no `sorry`, `admit`, new axiom, unsafe declaration, `native_decide`, or numerical cutoff computation.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauCanonical.lean` | `0049d1f97e3e5d25962cafd667ca4e35137aa8ef6239bf08a9730ddc59aa33cb` |
| `lean-statements/NLA/Proofs/MF03/FiniteRectDetTableau.lean` | `e6e11ca2b94ad996a90e295e854d0eaee211b2c7c17c832f70db4caadab91114` |
| `lean-statements/NLA/Proofs/MF03/FiniteDeterminantLimit.lean` | `dae4fe36fa8483141b5b96e76f4a7dc58a30f2d508bb405ea58ef015413577d7` |

The original Padé disk bound and full MF-03 Target remain open after determinant positivity; coefficient transfer and numerator estimates are separate reviewed gates.
