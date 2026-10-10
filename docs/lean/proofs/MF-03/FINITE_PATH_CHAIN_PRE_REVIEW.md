# MF-03 finite dual Jacobi–Trudi bridge: path-chain precontract

**Status:** proposed exact mathematical and numerical contract for independent
review before any Lean implementation. It follows the kernel-checked finite
bidiagonal-minor gate and precedes the still unproved tableau bijection.
The canonical MF-03 README, permanent ID, and frozen Target are unchanged.

## Existing exact matrix identity

Use the definitions and theorem in the frozen
`NLA.Proofs.MF03.FiniteBidiagonalMinor` at SHA-256
`8f97605566f879da87fb06c634ecc3b151c61f97cdb79c568d8f9ca6f295e44a`.
For `m,N : ℕ`, let `L=2m+1`, `a_k=cosineFactor(k+1)`, and `B_k` have
diagonal entries `1` and superdiagonal entries `a_k`. The product is
`P_N=B_(N−1)⋯B_0`, and

```text
P_N(i,h) = e_N(h−i) if i≤h, and 0 otherwise.
```

The augmented determinant is the minor with sorted row map
`I_(m,j)(p)=p` for `p<j` and `p+1` otherwise, and sorted column map
`J_m(p)=m+1+p`, for `0≤j≤m`. The rectangle is `j=0`. All indices are
zero-based and the missing starting row is `j`.

## Stage 1: exact one-factor minors

Let `StrictRows m` be the finite type of strictly increasing maps
`X : Fin m → Fin L`. The subtype includes its proof of strict monotonicity;
no arbitrary permutation of rows or columns is allowed. For `X,Y` in this
type, define

```text
valid(X,Y) :⇔ ∀ p : Fin m,
  Y(p).val = X(p).val  or  Y(p).val = X(p).val+1.

step_k(X,Y) = 0,                         if not valid(X,Y),
            = ∏_{p : Fin m} [1 if stationary, a_k if advanced],
                                           if valid(X,Y).
```

Prove the exact identity, for **all** `m,k,X,Y`, including `m=0`:

```text
det (B_k.submatrix X Y) = step_k(X,Y).                  (S)
```

The proof must expand the determinant enough to establish that a nonzero
matching is order preserving: if `p<q`, the possible columns of row `p`
are at most `X(p)+1≤X(q)`, while those of row `q` are at least `X(q)`.
Strictly increasing selected columns preclude a crossing matching. Hence
the only potentially nonzero determinant permutation is the identity, with
sign `+1`; it has precisely the stated stationary/advance factors. In
particular the result is nonnegative because each actual `a_k>0`.
This fact is not to be inferred by naming the determinant a path weight.

## Stage 2: one-step Cauchy–Binet and finite chains

Prove, for arbitrary real `L×L` matrices `A,C` and strictly increasing
`X,Z : Fin m→Fin L`, the **finite** minor Cauchy–Binet identity

```text
det ((A*C).submatrix X Z)
  = ∑_{Y : StrictRows m}
      det (A.submatrix X Y) * det (C.submatrix Y Z).   (CB)
```

Every `m`-element subset of `Fin L` has one sorted map `Y`; this is why
there is no factorial multiplier. A proof specialized to `L=2m+1` and
`ℝ` is acceptable. Pinned Mathlib has the square `Matrix.det_mul` but no
located ready minor Cauchy–Binet theorem; the identity must be derived in
Lean, not assumed.

Define a finite path chain from `X` to `Z` across `N` factors as a sequence
of strictly increasing position maps

```text
X_0=X, X_1, …, X_N=Z,
valid(X_t,X_(t+1)) for every 0≤t<N.
```

Its exact weight is

```text
∏_{t=0}^{N−1} step_(N−1−t)(X_t,X_(t+1)).
```

The first transition uses `B_(N−1)`, because the existing product is
`B_(N−1)⋯B_0`; reversing the factor labels would change the fixed weights
in the eventual tableau map. From (S) and (CB), prove, for arbitrary
`m,N,X,Z`, that `det (P_N.submatrix X Z)` is the sum of these finite
chain weights. For `N=0` there is a single length-zero chain of weight
`1` precisely when `X=Z`, and no chains otherwise. For `m=0`, the empty
minor and unique empty-position chain both have weight `1`.

The bounded public outputs may be factored into separate Lean modules:

```lean
theorem finiteBidiagonal_minor_eq_step (m k : ℕ)
    (X Y : StrictRows m) :
    Matrix.det (Matrix.submatrix (finiteBidiagonal m k) X.1 Y.1) =
      finiteStepWeight m k X Y

theorem finiteMinor_cauchyBinet (m : ℕ)
    (A C : Matrix (Fin (2*m+1)) (Fin (2*m+1)) ℝ)
    (X Z : StrictRows m) :
    Matrix.det (Matrix.submatrix (A*C) X.1 Z.1) =
      ∑ Y : StrictRows m,
        Matrix.det (Matrix.submatrix A X.1 Y.1) *
          Matrix.det (Matrix.submatrix C Y.1 Z.1)

theorem finiteProduct_minor_eq_chainSum (m N : ℕ)
    (X Z : StrictRows m) :
    Matrix.det (Matrix.submatrix (finiteBidiagonalProduct m N) X.1 Z.1) =
      finiteChainSum m N X Z
```

The exact Lean names/types may be adjusted for implementation, but the
mathematical values, matrix dimensions, ordered endpoints, and full
`m,N` quantification may not be weakened. The one-factor lemma should be
independently reviewed and kernel checked before the Cauchy–Binet/chain
source is written.

## Remaining tableau identity, excluded from this contract

For the endpoint `X=I_(m,j)`, `Z=J_m`, path `p` advances exactly
`J_m(p)−I_(m,j)(p)`: `m+1` times when `p<j` and `m` otherwise. These are
the column lengths of the existing shape `(m^m,j)`. If the advance
factor labels of path `p` are sorted increasingly, they are the labels
top-to-bottom in tableau column `p`; strictness within columns follows
because a path takes at most one step per factor. The noncollision
conditions should give weak increase across tableau rows. The reverse
construction and exact weight preservation still require a separate
kernel proof. Neither (S), (CB), nor the chain sum alone identifies the
determinant with `finiteAugTableauSum` or proves MF-03 Target.

For `m=2,j=1,N=3`, the endpoint starts at `{0,2}` and ends at `{3,4}`.
Its first path advances three times and second advances twice, matching
the two column lengths `3,2` of `(2,2,1)`; the canonical tableau with
columns `(0,1,2)` and `(0,1)` is one of the chains. This is only an
indexing check, not a computation-based proof.

## Source locks and verification rule

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `docs/lean/proofs/MF-03/SCHUR_PADE_ALL_ORDER_PRE_REVIEW.md` | `122a73c48b82f4468875045eb22ebb3383af682b915da2d7af83246f80ed0eed` |
| `docs/lean/proofs/MF-03/FINITE_BIDIAGONAL_MINOR_PRE_REVIEW.md` | `afc21ffbc1fe1f02af76aafa0fbd5f9edf5c47a297eb44f26707b572bd6c0fbe` |
| `lean-statements/NLA/Proofs/MF03/FiniteBidiagonalMinor.lean` | `8f97605566f879da87fb06c634ecc3b151c61f97cdb79c568d8f9ca6f295e44a` |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauTail.lean` | `245226b8e05f0aaa15d41a491ec74825a624db02a68a68e6f0741321ef49307d` |

Each implemented stage requires pinned Lean 4.33.1 direct build, exact
signature/imported LeanCert kernel audit, and an axiom audit. No `sorry`,
`admit`, new axiom, `native_decide`, or order-specific enumeration may
bridge a missing generic combinatorial argument.
