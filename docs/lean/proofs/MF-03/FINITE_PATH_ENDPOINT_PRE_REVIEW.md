# MF-03 finite path endpoints and tableau-bijection precontract

**Status:** exact mathematical and numerical contract for independent review
before its Lean implementation. It extends the already approved finite
path-chain contract. The canonical MF-03 README, permanent ID, and frozen Target
remain unchanged.

## Locked inputs

Use `finiteMinorRow`, `finiteMinorCol`, and
`finiteCosineAugDet_eq_bidiagonal_minor` from `FiniteBidiagonalMinor.lean`,
`StrictRows` from `FiniteBidiagonalStep.lean`, and the literal valid-chain sum
`finiteValidPathSum` and theorem `finiteProduct_minor_eq_validPathSum` from
`FinitePathChain.lean`. The latter has source SHA-256
`33607688166f0ef956360b026cd24cc08d0fe9815a0496eabe3753682a0bb09e`
and remains unimported pending independent imported audit. Also use the exact
`finiteAugShape`, `FiniteTableau`, and `finiteAugTableauSum` definitions in
`FiniteTableauTail.lean`.

All results below quantify **all** `N,m,j : ℕ` with `j ≤ m`. There is no
assumption that `N ≥ m`, no fixed-order enumeration, and no replacement by a
sign or inequality statement. Empty cases `m=0`, `N=0`, `j=0`, and `j=m`
remain in scope.

## Endpoint gate

Set `L=2m+1`. Both maps below are strictly increasing, so each determines
an element of `StrictRows m`:

```text
I_(m,j)(p) = p       if p < j,
             p + 1   if p ≥ j;

J_m(p) = m + 1 + p,  0 ≤ p < m.
```

For `j=0`, `I` omits row zero; for `j=m`, it omits row `m`. For `m=0`, both
maps are the unique empty map. Prove the exact endpoint identity

```text
finiteCosineAugDet N m j
  = finiteValidPathSum m N I_(m,j) J_m.             (E)
```

This is the direct combination of the existing determinant/minor identity
and the literal valid-chain theorem; the Lean proof must show that the
submatrix row and column maps are precisely the maps above. It must not
modify the determinant definition or transpose the endpoints.

## Column advance counts and factor labels

For each path `p : Fin m`, its total number of advances is exactly

```text
d_p = J_m(p).val - I_(m,j)(p).val
    = m + 1  if p < j,
      m      if p ≥ j.
```

The same values are the column lengths of `finiteAugShape m j`: columns
`p<j` include rows `0,...,m`, and columns `p≥j` include rows `0,...,m-1`.
For `j=0`, every column has length `m`; for `j=m`, every column has length
`m+1`. The formula also holds vacuously for `m=0`.

The `N` transitions are traversed in chronological order `t=0,...,N-1`;
transition `t` is the factor `B_(N-1-t)` and carries the zero-based label
`k=N-1-t`. A path advances at most once per factor. For each path `p`, sort
its advance labels increasingly and put them, in that order, down tableau
column `p`. This gives strict increase down columns. The weight of an
advance with label `k` is exactly `cosineFactor(k+1)`; a stationary move has
weight `1`. Thus the whole path-chain weight is the product of
`cosineFactor(T(r,p)+1)` over all cells of the augmented shape, exactly the
weight in `finiteAugTableauSum N m j`.

## Noncollision versus tableau rows

Let `S_p ⊆ Fin N` be the advance-label set for path `p`, with
`|S_p|=d_p`. At a cut `q` in the factor labels (`0 ≤ q ≤ N`), let
`A_p(q)=|{k∈S_p : q≤k}|`. Its position after the factors with labels
`N-1,...,q` is `I_(m,j)(p)+A_p(q)`. Adjacent strictness at **every** cut is
equivalent to

```text
A_p(q) ≤ A_(p+1)(q) + ε_p,
ε_p = 1 if p+1=j, and 0 otherwise.            (NC)
```

The only extra starting gap is across the omitted row `j`. With the fixed
set cardinalities, (NC) for every cut is equivalent to weak increase across
every existing tableau row:

```text
T(r,p) ≤ T(r,p+1)
```

whenever both `(r,p)` and `(r,p+1)` are cells. This equivalence needs a
separate Lean proof for generic `m,N,j`; it must not be inferred from a
picture or tested only at small orders. In particular the strict-row
condition must hold at intermediate positions, not just endpoints.

## Required bijection and exact equality

Construct mutually inverse maps between the literal valid chains from
`I_(m,j)` to `J_m` and `FiniteTableau (finiteAugShape m j) N`, using the
column-label construction above. Prove that both maps preserve every
zero-based label and the exact product weight. Then prove, for all
`N,m,j` with `j≤m`, the full identity

```text
finiteValidPathSum m N I_(m,j) J_m
  = finiteAugTableauSum N m j.                    (T)
```

Combining (E) and (T) yields

```text
finiteCosineAugDet N m j = finiteAugTableauSum N m j.  (JT)
```

The rectangle is the existing `j=0` case of the same assertion. Neither
endpoint equation alone nor a sum over unrestricted chains is (T) or (JT).
The zero-label case `N=0` must agree on both sides: only the empty shape
(`m=0`) has a tableau/chain, and its weight is `1`.

The implementation may split the endpoint, advance-count, row-condition,
bijection, and weighted-sum results into separate new modules. Freeze and
independently audit each stage before importing it into the aggregate.

## Source locks and verification

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `docs/lean/proofs/MF-03/SCHUR_PADE_ALL_ORDER_PRE_REVIEW.md` | `122a73c48b82f4468875045eb22ebb3383af682b915da2d7af83246f80ed0eed` |
| `docs/lean/proofs/MF-03/FINITE_PATH_CHAIN_PRE_REVIEW.md` | `1389c1e61c4f67388d996dc1990beca46cd9c833fd7909e9ec8cbdcb2e151bb8` |
| `lean-statements/NLA/Proofs/MF03/FinitePathChain.lean` | `33607688166f0ef956360b026cd24cc08d0fe9815a0496eabe3753682a0bb09e` |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauTail.lean` | `245226b8e05f0aaa15d41a491ec74825a624db02a68a68e6f0741321ef49307d` |

Every implemented stage requires pinned Lean 4.33.1 direct build, exact
signature/imported LeanCert kernel audit, and axiom audit. No `sorry`,
`admit`, new axiom, `native_decide`, or order-specific enumeration may
bridge the combinatorial argument.
