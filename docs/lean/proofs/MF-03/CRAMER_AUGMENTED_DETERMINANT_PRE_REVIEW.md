# MF-03 exact Cramer numerator and original augmented determinant

**Status:** source-locked mathematical and indexing precontract for an
independent review before the Lean implementation. This is an identity for the
actual Cramer vector and the already proved original infinite determinant. It
does not yet construct a normalized or reduced Padé pair.

## Exact contract

For every `m : ℕ` and `c : Fin m`, the original real Toeplitz matrix and
right-hand side from `PadeToeplitzCramer.lean` are

```text
T(r,c) = cosineElementaryCoeff (m + r.val - c.val),
b(r)   = -cosineElementaryCoeff (m + r.val + 1).
```

The Cramer coordinate is the determinant of `T.updateCol c b`, without
division. Put `j=c.val+1`, so `1≤j≤m`. The original infinite augmented
determinant is exactly

```text
cosineAugDet m j
 = det (fun r v : Fin m =>
     cosineElementaryCoeff
       (m + (if r.val < j then 1 else 0) + v.val - r.val)).
```

Prove this exact public theorem, with no added assumptions:

```lean
theorem cosinePadeToeplitz_cramer_eq_augDet (m : ℕ) (c : Fin m) :
    (cosinePadeToeplitz m).cramer (cosinePadeRHS m) c =
      (-1 : ℝ) ^ (c.val + 1) * cosineAugDet m (c.val + 1)
```

This includes `m=1`, `c=0` and `c=m-1`; at `m=0` there is no `c`, so the
statement is vacuous. The sign exponent is **`j=c.val+1`**, not `c.val`.
The determinant is the original `cosineAugDet`, not a finite-cutoff
determinant, a tableau sum, or a ratio.

## Matrix and index check

By `Matrix.cramer_apply`, the left side is `det (T.updateCol c b)`.
Transpose. Its row `k=c` consists of `-e_(m+v+1)`, and its other row
`k` consists of `e_(m+v-k)`, where `v` is the zero-based column and
`e_n=cosineElementaryCoeff n`. Reorder the transposed rows by the
permutation `(Fin.cycleRange c).symm`. Its new row 0 is old row `c`;
new rows `1,…,c` are old rows `0,…,c−1`; rows above `c` remain in place.
Thus the reordered matrix equals the original augmented matrix with its
first row multiplied by `−1`:

```text
new row 0:       -e_(m+v+1)                = -augmented row 0;
new rows 1..c:   e_(m+v-(r-1))           = augmented row r;
new rows c+1..:  e_(m+v-r)               = augmented row r.
```

All natural-number subtractions are nontruncating: every old row index is
`<m`, so `m+v≥oldRow`; every new row index is `<m`, so `m+δ+v≥newRow`.
`Fin.sign_cycleRange` gives the row-permutation sign `(-1)^c`; multiplying
the first augmented row by `−1` adds one minus sign. Since the sign is its
own inverse, `det (T.updateCol c b)=(-1)^(c+1) cosineAugDet m (c+1)`.

The manuscript states precisely this negative RHS and `j−1` column moves.
For an independent numerical sign check, the existing broader source review
records `m=1: q₁=-1/12`, and `m=2: q₁=-11/252`, `q₂=13/15120`.
No numerical check is used in the Lean proof.

## Scope and next gate

The already kernel-proved `cosinePadeToeplitz_det m` identifies `det T` with
`cosineRectDet m`, and `cosineRectDet_pos m` proves it positive. Once this
identity is proved, division gives the exact nonconstant denominator
coefficient `(-1)^j * cosineAugDet m j / cosineRectDet m`; the separately
audited `cosineAugDet_ratio_bounds` then gives the coefficient-one tail
bound. Constructing the polynomial, proving all Padé equations, reducing the
pair, and applying the disk estimate are separate obligations. This gate must
not claim the frozen `Target` or import any unproved identity.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/NLA/Proofs/MF03/FiniteDeterminantLimit.lean` | `dae4fe36fa8483141b5b96e76f4a7dc58a30f2d508bb405ea58ef015413577d7` |
| `lean-statements/NLA/Proofs/MF03/PadeToeplitzCramer.lean` | `059f68a79245756e5bb662dfb8cf373630c07a291396f1782d66d999f1f0f50f` |
| `lean-statements/NLA/Proofs/MF03/OriginalDeterminantRatio.lean` | `6e9399a531f60d6f9098788415f99c1a89232e7197bb25236238b3df86693b55` |

After independent mathematical approval, implement only the exact theorem in
a separate Lean module, then request an independent imported signature,
source, and axiom audit under LeanCert kernel before aggregate import. No
`sorry`, `admit`, new axiom, `native_decide`, unsafe declaration, or
per-order computation is permitted.
