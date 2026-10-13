# MF-03 exact nonconstant Padé coefficients from the original determinants

**Status:** source-locked mathematical, indexing, sign, and coefficient-one
contract for independent review before Lean implementation. The polynomial
pair and frozen all-order disk Target remain separate gates.

## Original system and exact definition

For every `m : ℕ`, the exact real high-degree Padé system has matrix
`T=cosinePadeToeplitz m`, `T(r,c)=e_(m+r−c)`, and right-hand side
`b=cosinePadeRHS m`, `b(r)=−e_(m+r+1)`. The unknown vector is the
**nonconstant** denominator coefficients `q_(c.val+1)` for `c:Fin m`.
The already kernel-proved determinant equality and positivity are

```text
det T = cosineRectDet m,       0 < cosineRectDet m.
```

Define a real vector by the literal Cramer quotient, with this same
positive determinant:

```lean
noncomputable def cosinePadeNonconstantCoeff (m : ℕ) (c : Fin m) : ℝ :=
  (cosinePadeToeplitz m).cramer (cosinePadeRHS m) c /
    cosineRectDet m
```

The original unnormalized Cramer equation `T *ᵥ cramer T b = det T • b`
then gives the **exact** normalized system

```lean
theorem cosinePadeNonconstantCoeff_system (m : ℕ) :
    (cosinePadeToeplitz m) *ᵥ cosinePadeNonconstantCoeff m =
      cosinePadeRHS m
```

There is no lower-dimensional substitute or assumption that the system
is already solved. The `m=0` vector is empty and the statement is valid.

## Exact signed coefficient and sharp bound

The independently audited original Cramer determinant theorem states,
for `j=c.val+1` (so `1≤j≤m`),

```text
cramer T b c = (−1)^j cosineAugDet m j.
```

Thus the exact source coefficient identity is

```lean
theorem cosinePadeNonconstantCoeff_eq_signed_ratio
    (m : ℕ) (c : Fin m) :
    cosinePadeNonconstantCoeff m c =
      (-1 : ℝ) ^ (c.val + 1) *
        (cosineAugDet m (c.val + 1) / cosineRectDet m)
```

The original determinant ratio is nonnegative and at most
`(cosineTail m)^j`, coefficient **one**, for every `j≤m`. Therefore

```lean
theorem cosinePadeNonconstantCoeff_abs_le_tail
    (m : ℕ) (c : Fin m) :
    |cosinePadeNonconstantCoeff m c| ≤
      (cosineTail m) ^ (c.val + 1)
```

The bound is on the actual signed coefficient's real absolute value,
not a finite cutoff or tableau proxy. Later coercion to complex must
preserve this value as the complex norm. The index begins at `j=1`,
ends at `j=m`, and is vacuous for `m=0`; the separately constructed
constant coefficient must be exactly `q₀=1`. No factor of 2, `m`,
or extra tail term is introduced. No claim is made about `P`, reduced
pairs, disk nonvanishing, or the frozen `Target` at this gate.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/NLA/Proofs/MF03/PadeToeplitzCramer.lean` | `059f68a79245756e5bb662dfb8cf373630c07a291396f1782d66d999f1f0f50f` |
| `lean-statements/NLA/Proofs/MF03/CramerAugmentedDeterminant.lean` | `6a6bd97db8034b1a81dc11189d483bc39e6d55580889f2f00d41b2cc60ba94c6` |
| `lean-statements/NLA/Proofs/MF03/RectDeterminantPositivity.lean` | `3b4e0239c569aebf3ac55e71100b7f455d686243a5ea7541b04e4a80dc249ceb` |
| `lean-statements/NLA/Proofs/MF03/OriginalDeterminantRatio.lean` | `6e9399a531f60d6f9098788415f99c1a89232e7197bb25236238b3df86693b55` |

Independently review all three exact signatures and the matrix/ratio
normalization before implementation. Then direct-check each theorem with
LeanCert kernel, freeze the source, and independently audit imported
signatures and axioms before aggregate import. No `sorry`, `admit`,
new axiom, `native_decide`, unsafe declaration, or per-order enumeration.
