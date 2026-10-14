# MF-03 all-order Schur/Padé gate: pre-implementation contract

This is an exact mathematical and numerical contract for the remaining
all-order denominator step. It requests independent review before any Lean
source is written. The canonical `MF-03` README, permanent ID, and frozen
`NLA.Statements.MF03.Target` are unchanged. No Schur identity is assumed in
that target or in the proposed final theorem.

## Exact output required

Use the existing `cosineElementaryCoeff` and `cosineTail` definitions, with
zero-based factor weights

```text
a_k = cosineFactor (k+1) = 1/[π²(k+1/2)²] > 0,       k = 0,1,...
e_n = cosineElementaryCoeff n = 1/(2n)!,
S_m = cosineTail m = ∑_{k=m}^∞ a_k.
```

The last equality for `e_n` is the exact theorem in the frozen
`CosineCoefficientTransfer.lean`, not a numerical approximation. Define the
following **real** determinants for `m ≥ 1` and `0 ≤ j ≤ m` (the displayed
formula uses `r,c : Fin m`, hence zero-based matrix indices):

```lean
noncomputable def cosineRectDet (m : ℕ) : ℝ :=
  Matrix.det (fun r c : Fin m =>
    cosineElementaryCoeff (m + c.val - r.val))

noncomputable def cosineAugDet (m j : ℕ) : ℝ :=
  Matrix.det (fun r c : Fin m =>
    cosineElementaryCoeff
      (m + (if r.val < j then 1 else 0) + c.val - r.val))
```

These natural subtractions do not truncate an intended negative index:
`r.val < m`, so `r.val ≤ m+c.val`. The augmented determinant has its first
`j` rows shifted by one. In particular `cosineAugDet m 0 = cosineRectDet m`.

The proposed public outputs, in namespace `NLA.Proofs.MF03`, are:

```lean
theorem cosineRectDet_pos (m : ℕ) (hm : 1 ≤ m) :
    0 < cosineRectDet m

theorem cosineAugDet_pos_tail (m j : ℕ)
    (hm : 1 ≤ m) (hj₁ : 1 ≤ j) (hj₂ : j ≤ m) :
    0 < cosineAugDet m j ∧
      cosineAugDet m j ≤
        cosineRectDet m * (cosineTail m) ^ j

theorem cosine_exists_normalized_with_tail (m : ℕ) (hm : 1 ≤ m) :
    ∃ P Q : Polynomial ℂ,
      NLA.Statements.MF03.NormalizedPadeRepresentation m P Q ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ m →
          Q.coeff j = (-1 : ℂ) ^ j *
            ((cosineAugDet m j / cosineRectDet m : ℝ) : ℂ) ∧
          ‖Q.coeff j‖ ≤ (cosineTail m) ^ j
```

The signed formula is part of the output and must be proved, not inferred
from a norm estimate. The witness theorem applies to every `m ≥ 1` and is
stronger than the coefficient hypothesis of the already proved
`largeOrder_disk_of_tail_coefficients` at `m ≥ 16`. The theorem supplies one
normalized pair; `normalized_exists_reduced` supplies a reduced pair, and
`disk_bound_for_every_reduced_pair` transports the disk result to **every**
reduced pair in the frozen Target. The existing `target_through_fifteen`
covers `1 ≤ m ≤ 15`.

## Gate 1: finite-variable determinant/tableau identity

For `N : ℕ`, define the finite elementary coefficient exactly by subsets of
`Finset.range N`:

```text
e_N(n) = ∑_{S ⊆ {0,...,N−1}, |S|=n} ∏_{k∈S} a_k.
```

Set `D_N(m,0)` and `D_N(m,j)` by replacing `e_n` with `e_N(n)` in the two
determinants above. Define finite weighted semistandard tableaux using
Mathlib's `SemistandardYoungTableau`, but restrict every cell label to `< N`;
this restriction must be made into an actual finite type or finite set. A
tableau's weight is the product of `a_(label)` over all cells. The two shapes
are the rectangle `(m^m)` and the rectangle plus a bottom row `(m^m,j)`.
Mathlib's tableau entries are zero-based, matching the `a_k` indices here.
The latter shape is used only for `1 ≤ j ≤ m`; a zero last row is omitted.

Prove the following **finite** dual Jacobi–Trudi specializations:

```text
D_N(m,0) = ∑_{T : SSYT_N(m^m)} weight(T),
D_N(m,j) = ∑_{T : SSYT_N(m^m,j)} weight(T),  1 ≤ j ≤ m.
```

No pinned Mathlib theorem appears to supply these identities directly.
Their proof is a genuine obligation: expand the finite determinants and
finite elementary coefficients, cancel intersecting path families by a
sign-reversing involution (or prove the equivalent finite dual
Jacobi–Trudi identity), and biject the surviving families with tableaux.
This is a generic finite combinatorial proof in `m,N,j`; it uses no large
rational certificates or per-order computation. The matrix indexing and
partition transposition must be checked in the Lean proof, not hidden in a
name `schur` without a derivation.

For `N ≥ m`, the rectangular tableau with row `r` filled by label `r`
exists and has strictly positive weight, so `D_N(m,0)>0`. For `N ≥ m+1`
and `1 ≤ j ≤ m`, extending it by a bottom row filled with `m` gives
`D_N(m,j)>0`.

## Gate 2: finite tableau restriction and the exact tail

Restrict each tableau of shape `(m^m,j)` to its rectangular first `m`
rows. Its extra bottom row has `j` weakly increasing labels. Column
strictness through the `m` cells above each extra cell forces every extra
label `k ≥ m` (equivalently manuscript label `ν=k+1>m`). For each fixed
rectangular tableau, valid extra rows form a subset of all weakly increasing
`j`-tuples from `{m,...,N−1}`. Restriction plus the extra tuple is injective,
and tableau weights factor into rectangle weight times extra-row weight.

Put `S_{m,N}=∑_{k=m}^{N−1}a_k` and let `h_{j,N}` be the sum of products over
weakly increasing `j`-tuples from the same range. Positivity gives

```text
0 < D_N(m,j) ≤ D_N(m,0) h_{j,N}
              ≤ D_N(m,0) S_{m,N}^j
              ≤ D_N(m,0) S_m^j
```

for `N ≥ m+1`, `1 ≤ j ≤ m`. The middle inequality expands the ordered
`j`-fold product `S_{m,N}^j`: each weakly increasing tuple occurs at least
once. The final inequality is monotonicity of the positive series tail.
For `N=m`, the augmented tableau sum is zero; this edge case need not be
used for augmented positivity. In particular **the tail starts at `k=m`**;
starting at `k=m+1` would be mathematically false here.

This finite restriction inequality can be implemented and kernel checked
before the determinant/tableau identity. It is the first bounded Lean gate
after contract approval. It must not be promoted to a determinant theorem
until Gate 1 is proved.

## Gate 3: infinite positive limit

For each fixed `n`, show `e_N(n) → e_n` as `N→∞`. The finite subset sums
exhaust the subtype sum defining `cosineElementaryCoeff n`; all terms are
nonnegative and summable by the finite-subset product argument in the
coefficient-transfer proof. Its summability helpers are private, so this
new module must reproduce the needed helper rather than refer to a hidden
declaration. The
determinants have fixed size `m`, so polynomial continuity of the finite
determinant expression gives `D_N(m,j) → cosineAugDet m j` and similarly
for the rectangle. The finite tableau identities make `D_N(m,0)` and
`D_N(m,j)` monotone in `N`. The positive canonical tableau weight therefore
gives a fixed positive lower bound from `N=m` (rectangle) or `N=m+1`
(augmented) onward. Passing the Gate 2 inequality to the limit proves
`cosineRectDet_pos` and `cosineAugDet_pos_tail`.

This route does **not** require defining an infinite tableau sum or proving
`S_{m,N}→S_m`: each finite bound already uses the fixed `S_m`.

## Gate 4: Cramer construction and frozen Padé equations

The unknown nonconstant denominator coefficients satisfy the finite
Toeplitz system, with `r,c : Fin m`:

```text
T(r,c) = e_(m+r−c),     b(r) = −e_(m+r+1),
T · (q_(c+1)) = b.
```

Here `det T = cosineRectDet m` by transposition, hence is nonzero. Pinned
Mathlib has `Matrix.cramer`, `Matrix.cramer_apply`, and
`Matrix.mulVec_cramer`. Cramer's replacement of column `j−1` by `b`, then
moving that column to the front, incurs `j−1` transpositions plus the
minus sign in `b`. After transposition the rows are shifted exactly as in
`cosineAugDet m j`. Thus the **exact** identity is

```text
q_0 = 1,
q_j = (−1)^j D(m,j)/D(m,0),   1 ≤ j ≤ m.
```

Checks: `m=1` gives `D(1,0)=e_1=1/2`, `D(1,1)=e_2=1/24`, and
`q_1=−1/12`. For `m=2`, `D(2,0)=1/960`,
`D(2,1)=11/241920`, `D(2,2)=13/14515200`, so
`q_1=−11/252` and `q_2=13/15120`. These are exact rational
index/sign checks, not substitutes for the all-order proof.

Define `Q(z)=∑_{j=0}^m q_j z^j` and let `P` be the degree-`m`
truncation of `Q(z)∑_{n≥0}e_n z^n`:

```text
P.coeff n = ∑_{i=0}^n q_i e_(n−i),  0 ≤ n ≤ m.
```

The Padé equations through `n=m` hold by construction. For
`n=m+r+1`, `r : Fin m`, they are exactly the Toeplitz system above,
because `P.coeff n=0` and `Q.coeff i=0` for `i>m`. Replace every `e_n`
by `1/(2n)!` using `cosineElementaryCoeff_eq_factorial`; this yields **all**
frozen equations `n≤2m`, including the endpoint. The determinant positivity
ensures `Q.coeff 0=1`, and the finite polynomial constructions ensure both
degree bounds. Positivity of the two determinants and the Gate 3 ratio bound
give

```text
‖Q.coeff j‖ = D(m,j)/D(m,0) ≤ (cosineTail m)^j,
```

which proves the public witness theorem. There is no extra hypothesis on
the frozen Target.

## Verification and source binding

Implement in new, initially unimported MF-03 proof modules, one gate at a
time. Direct pinned Lean 4.33.1 builds and LeanCert kernel checks are
required. No `sorry`, added axiom, `native_decide`, weakened theorem, or
large finite enumeration may bridge a missing generic identity. A module
may be reported as partial only with its proved scope stated explicitly.
Coordinate the shared Lake build window with the SP-14 and TR-14 agents.

SHA-256 at contract creation:

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `docs/lean/proofs/MF-03/ALL_ORDER_SOURCE_OBLIGATIONS.md` | `96399593ee86dedb1020da3f9d9301e865c82eec1c801917edcf587e59a58aa6` |
| `lean-statements/NLA/Proofs/MF03/CosineCoefficientTransfer.lean` | `b17175f8a9ed18507e98beffe08cb7d02fb802380437155aafb518c0dc05da60` |
| `lean-statements/NLA/Proofs/MF03/CosineTail.lean` | `41fc5b7da2f1033b17608a56507aeeba555099f933a1b5eea05477331e8ace8b` |
| `lean-statements/NLA/Proofs/MF03/LargeOrderDisk.lean` | `0bd595d22ae9237d608cfe9bf1e521e3ca5869df83ea729e8862e98ef493c7ec` |
| `lean-statements/NLA/Proofs/MF03/Reduction.lean` | `0e58cdba5a4302aa025201e73143a4c3056f33fc43c618da6bf4aa0095da89cb` |
| `lean-statements/NLA/Proofs/MF03/Transport.lean` | `902e6c7caf52f462d2bc11fcdf713306f69d67d8da0a159b01713ae31fc6cb66` |
| `lean-statements/NLA/Proofs/MF03/Uniqueness.lean` | `c781644e76a6143535a45862263e6776ee1257ff6ac2d69eed328dd63f73daa5` |

Independent review should verify the two finite dual Jacobi–Trudi shapes,
zero-based subtraction and tail indices, canonical tableau positivity,
Cramer sign, every Padé equation through `2m`, and the exact later
composition with `Target`. The main implementation risk is Gate 1: pinned
Mathlib provides tableaux and Cramer tools but no ready dual
Jacobi–Trudi theorem or Lindström–Gessel–Viennot lemma.
