# MF-03 finite uniform-column sentinel precontract

**Status:** exact mathematical, indexing, and numerical precontract for
independent review before implementing the uniform-column tableau map. This
refines the approved endpoint/tableau contract without changing its target,
factor order, tableau shape, or canonical MF-03 statement.

## Source-locked input

Fix arbitrary `N,m,j : ℕ` with `j ≤ m`. A valid path chain starts at
`I_(m,j)` and ends at `J_m` exactly as in
`FINITE_PATH_ENDPOINT_PRE_REVIEW.md`. The frozen path-label and cut modules
show that its advance-label sets `S_p ⊆ {0,...,N-1}`, indexed by
`p : Fin m`, have cardinality

```text
|S_p| = d_p = m+1 if p<j, and m if p≥j,
```

and obey, at every cut `q` with `0≤q≤N`,

```text
|{k∈S_p : q≤k}| ≤ |{k∈S_(p+1) : q≤k}| + [p+1=j]
```

for every adjacent `p,p+1`. Here `[P]` is `1` if `P`, otherwise `0`.
The omitted starting row is exactly `j`; no factor labels or path indices
are reversed.

## Uniform augmentation by a sentinel

Define a temporary **sentinel** label `N` and sets

```text
U_p = S_p                  if p<j,
      S_p ∪ {N}            if p≥j.
```

Every actual advance label is `<N`, hence the sentinel is fresh whenever
inserted. Consequently `|U_p|=m+1` for every `p`. Every element of `U_p`
is `≤N`, and `N∈U_p` exactly when `p≥j`. Let

```text
u_p : Fin (m+1) → ℕ
```

be the unique strictly increasing enumeration of `U_p`. For `p≥j`, its
last entry is `u_p(m)=N`; every earlier entry is `<N`. For `p<j`, all
`m+1` entries are actual labels `<N`.

At a cut `q≤N`, the exact suffix count is

```text
|{k∈U_p : q≤k}|
  = |{k∈S_p : q≤k}| + [p≥j].
```

At `q>N`, both suffix counts are zero. For adjacent columns the only
change in `[p≥j]` occurs at `p+1=j`, so the source-locked path inequality
becomes the **equal-length** inequality

```text
|{k∈U_p : q≤k}| ≤ |{k∈U_(p+1) : q≤k}|       for every q∈ℕ.
```

The frozen generic equal-length order-statistics theorem then gives

```text
u_p(r) ≤ u_(p+1)(r)  for all r : Fin (m+1).
```

This equality of count and row formulations must be proved, not assumed
from a diagram or small-order computation.

## Exact map to the original finite tableau

Define the tableau on the **unchanged** `finiteAugShape m j` by

```text
T(r,p) = u_p(r)  when (r,p) is a cell of finiteAugShape m j,
         0       outside the shape.
```

The shape has all cells `r<m,p<m` and exactly the bottom cells `r=m,p<j`.
For `p≥j`, `(m,p)` is **not** a cell: the sentinel `u_p(m)=N` is discarded
there and must never enter `FiniteTableau`, `finiteAugTableauSum`, or a
cosine factor. Every actual cell entry is `<N`. The strict enumeration
proves column strictness; the equal-length row inequality proves weak rows
for all existing adjacent cells, hence all rows. Thus the map has codomain
the existing `FiniteTableau (finiteAugShape m j) N` without changing that
definition.

Conversely, for an existing finite augmented tableau `T`, form `S_p`
from the actual entries in column `p` (all rows `0,...,m` if `p<j` and
rows `0,...,m-1` otherwise), and add the sentinel `N` only when `p≥j`.
Column strictness and `<N` make the entries distinct, give the exact
cardinalities, and ensure that their sorted enumeration reproduces `T`.
Weak tableau rows give the uniform `u_p(r)≤u_(p+1)(r)` for all
`r:Fin(m+1)`; at bottom crossings to a short column the right entry is
the sentinel `N`, and between short columns both bottom entries are `N`.
The equal-length count theorem returns the source-locked noncollision
inequalities after removing the sentinel.

## Converse reconstruction of the literal valid path chain

From the recovered actual sets `S_p` (with sentinel removed), define,
for each integer cut `q` with `0≤q≤N`,

```text
P_q(p) = I_(m,j)(p) + |{k∈S_p : q≤k}|.
```

The construction must prove **in Lean** all of the following before
claiming a chain inverse:

1. `P_q(p) < 2m+1` for every `p,q`. Indeed the suffix count is at most
   `|S_p|=J_m(p)−I_(m,j)(p)`, so `P_q(p)≤J_m(p)≤2m`.
2. `p↦P_q(p)` is strictly increasing for every cut. Adjacent strictness
   is exactly the original noncollision inequality with the starting gap
   `2` only at `p+1=j`; strictness for arbitrary `p<p'` follows by
   transitivity.
3. `P_N=I_(m,j)` because no actual label reaches `N`, and `P_0=J_m`
   because every actual label is nonnegative and the prescribed set
   cardinalities equal the endpoint displacements.
4. For every `q` with `1≤q≤N`, the transition from `P_q` to `P_(q−1)`
   is stationary or one advance in each coordinate. Its advance
   indicator for path `p` is precisely membership of `q−1` in `S_p`.
   This transition carries factor label `q−1`, so the chronological
   chain is `P_N,P_(N−1),...,P_0` and has exactly `N` steps.

Recursively assemble these maps and validity proofs into the existing
`FiniteValidPath m N I_(m,j) J_m` type. Extracting advance-label sets from
the resulting chain must return the original `S_p`, and reconstructing
from the label sets of an existing valid chain must return that original
chain. The frozen cut-position theorem provides the latter equality at
every cut. These inverse proofs include `N=0`: there is only one cut,
and the endpoint equations can hold only for the empty shape `m=0`.
For `m=0`, the maps and label-set family are unique and the empty chain
is reconstructed for every `N`.

The tableau/column-system and column-system/path constructions together
must form the claimed mutual bijection, not merely injections or
weight-preserving maps in one direction.

## Weight and boundary requirements

The literal valid-chain weight is already the product of
`cosineFactor(k+1)` over each actual `S_p`. Since the sentinel is
discarded, the tableau weight is exactly

```text
∏_{(r,p)∈finiteAugShape m j} cosineFactor(T(r,p)+1),
```

which is definitionally represented in the existing
`finiteAugTableauSum N m j` by its rectangular and bottom-row products.
There must be no extra `cosineFactor(N+1)` factor. A proof of equality of
finite weighted sums must use the mutual bijection and this exact weight
identity, for **all** `N,m,j` with `j≤m`.

Boundary checks are part of the generic proof:

- `j=0`: all columns are short and receive a sentinel; there is no bottom
  tableau row.
- `j=m`: all columns are long and receive no sentinel.
- `m=0`: there are no columns, the empty chain and empty tableau each have
  weight `1` for every `N`.
- `N=0,m>0`: the required positive column cardinality is impossible, so
  both path and tableau sets are empty and both weighted sums are `0`.

The implementation may factor these claims into new modules for uniform
sets, sorted rows, tableau maps, inverse maps, and weighted-sum transport.
Each source stage is frozen for independent exact imported audit before
aggregate import. No original README, permanent ID, frozen Target, or
existing numerical coefficient may be altered.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `docs/lean/proofs/MF-03/FINITE_PATH_ENDPOINT_PRE_REVIEW.md` | `c758075048eb1c31f6d2ea6c34a5c62e567c469ae7dfe2b7326b467f90a7406b` |
| `lean-statements/NLA/Proofs/MF03/FinitePathLabels.lean` | `03a60687fa2ffa5c6a87857bd541b70256276b138951a58fac9979b5e8c09b60` |
| `lean-statements/NLA/Proofs/MF03/FinitePathWeight.lean` | `5254564d9a0540c284c127dc9ec4f656f4dfa66ba386a5a3faf62937ea0adefe` |
| `lean-statements/NLA/Proofs/MF03/FinitePathCuts.lean` | `40332d778cd3b352fab350a256b8afa801c7cf699fc391ca720f3d3519295c7a` |
| `lean-statements/NLA/Proofs/MF03/FiniteColumnOrder.lean` | `a95f3b09356365f4652ff0352f41b97ab031a2e968c74de3c900e1c15ae0c4c6` |
| `lean-statements/NLA/Proofs/MF03/FiniteColumnCuts.lean` | `7dc31533a896032c1d9c99e2c5213a82c471cbec9149d4fdc230fd3f5a1c9252` |
| `lean-statements/NLA/Proofs/MF03/FiniteColumnSorted.lean` | `189195f34c69c592d240e28575baa29d6e7adf9f3e40a797d5b590bb5b355801` |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauTail.lean` | `245226b8e05f0aaa15d41a491ec74825a624db02a68a68e6f0741321ef49307d` |

Pinned Lean 4.33.1 direct build, exact imported LeanCert kernel audit, and
axiom audit remain required. No `sorry`, `admit`, new axiom,
`native_decide`, or order-specific enumeration is permitted.
