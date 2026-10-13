# MF-03 finite dual Jacobi–Trudi bridge: bidiagonal-minor precontract

**Status:** exact mathematical and numerical statement awaiting independent
pre-implementation review. This is a bounded first bridge from the finite
elementary determinants to a finite path model. It does not assert the
determinant/tableau identity, determinant positivity, or the all-order target.

## Fixed source and indexing

The manuscript uses positive variables `t_ν`, indexed from `ν=1`. Here
`a_k = cosineFactor (k+1) = t_(k+1)` has zero-based index `k`. The existing
`finiteCosineElementaryCoeff N d` is exactly the sum of `∏_{k∈S} a_k` over
`S ⊆ Finset.range N` of cardinality `d`, including `e_N(0)=1` and
`e_N(d)=0` for `d>N`.

For arbitrary `m,N : ℕ`, put `L=2*m+1` and define an `L × L` upper
bidiagonal matrix over `ℝ` for each `k`:

```text
B_k(i,h) = 1      if h=i,
         = a_k    if h=i+1,
         = 0      otherwise,       i,h : Fin L.
P_0 = I_L,          P_(N+1) = B_N P_N.
```

Thus `P_N=B_(N−1)⋯B_1 B_0`, so a path takes at most one right step in each
factor and the step at factor `k` has the **actual** weight `a_k`. The order is
descending from left to right; the matrices commute because they are
polynomials in one shift, but this commutation is not needed for the first
gate. The exact entry identity is

```text
P_N(i,h) = if i≤h then e_N(h−i) else 0.             (E)
```

The `i>h` case is essential: natural subtraction would otherwise return
zero and incorrectly give `e_N(0)=1` below the diagonal. Prove (E) from the
finite-subset recurrence

```text
e_(N+1)(d) = e_N(d) + a_N e_N(d−1),   d≥1,
e_(N+1)(0) = e_N(0) = 1,
```

including the `i=h` and last-row boundaries. The recurrence must be proved
from `powersetCard` membership by whether the new index `N` belongs to the
subset; it is not a new assumption. This is uniform in `m,N,d`, with no
per-order enumeration.

For `r,c : Fin m` and `0≤j≤m`, use strictly increasing row and column maps
into `Fin L`:

```text
I_(m,j)(r) = if r<j then r else r+1,
J_m(c)     = m+1+c.
```

They have `m` distinct indices and satisfy `I_(m,j)(r) ≤ J_m(c)` for every
`r,c` (also at `j=0` and `j=m`). Equation (E) gives the exact entry equality

```text
P_N(I_(m,j)(r), J_m(c))
  = e_N(m + [r<j] + c − r),
```

where `[r<j]` is `1` or `0`. Therefore the proposed public endpoint of this
bounded Lean gate is

```lean
theorem finiteCosineAugDet_eq_bidiagonal_minor
    (N m j : ℕ) (hj : j ≤ m) :
    finiteCosineAugDet N m j =
      Matrix.det (fun r c : Fin m =>
        finiteBidiagonalProduct m N
          (finiteMinorRow m j r) (finiteMinorCol m c))
```

where the three new definitions must implement `B_k`, `P_N`, `I_(m,j)`, and
`J_m` exactly as above. The rectangular specialization at `j=0` must also
be proved using the existing `finiteCosineAugDet_zero`; this is the same
minor with row set `{1,…,m}` and column set `{m+1,…,2m}`. At `j=m` the row
set is `{0,…,m−1}`. The augmented row set for intermediate `j` is
`{0,…,j−1} ∪ {j+1,…,m}`. In particular, the missing row is **`j`**.

The matrix dimension `2m+1` is exact: the final column at `c=m−1` is
`2m`, and no entry beyond it is used. For `m=0`, both determinants are empty
and the identity still holds; no positivity claim is inferred from this
edge case.

## Subsequent bridge obligation, excluded from this gate

Cauchy–Binet applied successively to `P_N` expands the minor into chains of
strictly increasing `m`-element position sets, each position advancing by
zero or one in a factor. An upper-bidiagonal minor has at most one nonzero
matching, so each chain has nonnegative weight, the product of its `a_k`
steps. At the endpoints above, the move counts of the `m` paths are `m+1`
for their first `j` positions and `m` for the others. These are the column
lengths of the conjugate partition `((m+1)^j,m^(m−j))`, whose Young diagram
is the existing `finiteAugShape m j = (m^m,j)`. The `j=0` shape is the
existing `finiteRectShape m`. A later kernel proof must biject these chains
with actual `FiniteTableau` values, preserve **each** `a_k` weight, and
deduce the finite dual Jacobi–Trudi identities. This precontract does not
admit that bijection as an axiom or a theorem premise.

For a quick index check at `m=2,j=1`, the row set is `{0,2}`, columns
`{3,4}`, and the entry matrix is

```text
[ e_N(3)  e_N(4) ]
[ e_N(1)  e_N(2) ],
```

which is exactly `finiteCosineAugDet N 2 1`; the rectangle has rows `{1,2}`
and entry matrix `[[e_N(2),e_N(3)],[e_N(1),e_N(2)]]`. These are symbolic
checks of indices, not finite numerical certificates.

## Implementation and review boundary

Implement this in a new `NLA.Proofs.MF03.FiniteBidiagonalMinor` module after
independent approval. Import the already reviewed
`NLA.Proofs.MF03.FiniteDeterminantLimit`; preserve all existing definitions
and the frozen target. Use pinned Lean 4.33.1 and `set_option leancert.trust
"kernel"`, with direct build, `#assert_trust kernel`, an independent exact
signature audit, and an axiom audit. This module is not a full proof of
MF-03 or of the finite tableau identity.

SHA-256 source locks at precontract creation:

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `docs/lean/proofs/MF-03/SCHUR_PADE_ALL_ORDER_PRE_REVIEW.md` | `122a73c48b82f4468875045eb22ebb3383af682b915da2d7af83246f80ed0eed` |
| `lean-statements/NLA/Proofs/MF03/FiniteElementaryLimit.lean` | `d8d28308b89e7dc6144b4b0aba7897008cac31630ce865a5eea2b3647b625989` |
| `lean-statements/NLA/Proofs/MF03/FiniteDeterminantLimit.lean` | `dae4fe36fa8483141b5b96e76f4a7dc58a30f2d508bb405ea58ef015413577d7` |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauTail.lean` | `245226b8e05f0aaa15d41a491ec74825a624db02a68a68e6f0741321ef49307d` |
