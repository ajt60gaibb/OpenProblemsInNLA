# MF-03 exact finite path weight and tableau sum transport

**Status:** source-locked mathematical and indexing contract for independent
review before implementing any new weight or weighted-sum identity in Lean.
This follows the exact path/column and column/tableau equivalences and
preserves the original augmented determinant and MF-03 target.

## Fixed domains, maps, and factor

Fix arbitrary `N,m,j : ℕ` with `hj : j ≤ m`. Write
`I = finitePathStart m j hj`, `J = finitePathEnd m`,
`P = FiniteValidPath m N I J`, and
`A = FiniteTableau (finiteAugShape m j) N`. The frozen equivalences are

```text
P ≃ FiniteColumnSystem N m j        (finiteColumnPathEquiv hj),
FiniteColumnSystem N m j ≃ A        (finiteTableauColumnEquiv N m j hj).
```

Their composition must be the exact path/tableau equivalence used for
finite sum transport. For a path `c`, let `D` be its actual
`finitePathToColumnSystem` and `T=finiteColumnSystemToTableau D hj`.
For each path coordinate `p : Fin m`, its actual zero-based factor-label
set is `S_p=D.labels p`. The factor for label `k` is exactly the real
number `cosineFactor (k+1)`, with no reindexing or normalization change.

## Exact per-column cell decomposition

The original augmented shape has upper cells `(r,p)` for `0≤r<m`,
`0≤p<m`; it has a bottom cell `(m,p)` precisely when `p<j`.
All tableau cell values are `<N`. The existing uniform-column device
has `m+1` values in each column; when `p≥j`, its last value is the
temporary sentinel `N` at `(m,p)`, which is **not a cell**.

For every `p : Fin m`, prove the literal finite-set equality

```text
S_p = { T(r,p) : 0≤r<m }
      ∪ (if p<j then {T(m,p)} else ∅).
```

The union is disjoint, because each real column is strictly increasing.
Equivalently, the values of the upper cells and the optional actual
bottom cell enumerate `S_p` exactly once. This equality must come from
the frozen `finiteColumnSystem_tableau_actualLabels` and the definitions
of `finiteTableauUniformValue` and `finiteTableauActualLabels`; it may
not count the short-column sentinel as an actual label. It covers
`m=0` vacuously and both `j=0` and `j=m` without separate enumeration.

Applying `f(k)=cosineFactor(k+1)` gives the exact per-column product

```text
∏ k∈S_p f(k)
  = (∏ 0≤r<m f(T(r,p)))
      · (if p<j then f(T(m,p)) else 1).
```

The empty product is `1`. No factor is divided out, cancelled, or
assumed nonzero: if any actual factor vanishes, both sides vanish.
For `p≥j`, there is no `f(N)=cosineFactor(N+1)` term at all.

## Literal path weight identity

The frozen path-weight theorem is

```text
finiteValidPathWeight m N I J c
  = ∏ p : Fin m, ∏ k∈S_p cosineFactor(k+1).
```

Use the per-column equality, finite-product distribution, and
commutation of the two finite upper-cell products to prove the exact
pointwise target

```text
finiteValidPathWeight m N I J c
  = finiteRectWeight m T.1 * finiteBottomWeight j m T.1.
```

The right side is precisely the summand in the existing
`finiteAugTableauSum N m j`; no new weight definition may replace it.
The product order has no mathematical effect because it is over real
numbers, but all row and column index sets must remain the original
`range m` and `range j`.

## Exact weighted-sum and determinant identities

The composed equivalence `P ≃ A` is a bijection, including when either
type is empty. Reindex the existing `finiteValidPathSum m N I J` along
this equivalence and apply the pointwise weight theorem. The required
finite weighted-sum identity is

```text
finiteValidPathSum m N I J = finiteAugTableauSum N m j.
```

The already frozen `finiteCosineAugDet_eq_validPathSum N m j hj`
then gives the public exact finite Jacobi–Trudi/path/tableau bridge

```text
finiteCosineAugDet N m j = finiteAugTableauSum N m j.
```

This is an equality of the original finite determinant and original
bounded augmented-tableau sum. It is not a positivity claim, a tail
estimate, or a numerical bound. Any later use of positivity must be
proved from the actual factor formula and the exact target in a
separate reviewed gate.

## Zero and boundary cases

- `m=0` forces `j=0`; the path, column system, and empty tableau are
  unique, and both weights and both sums are `1` for every `N`.
- `N=0,m>0`: each actual label set would need `m` or `m+1` distinct
  labels below zero, so the path and tableau domains are empty. Both
  weighted sums are zero; the determinant identity follows through
  the frozen path-sum theorem, without an order-specific computation.
- `j=0`: all columns have length `m`; the bottom product is an empty
  product, equal to `1`.
- `j=m`: every column has a genuine bottom cell; no sentinel is used.
- A zero actual factor makes exactly the corresponding path and
  tableau summands zero. The proof must remain valid without a
  nonzero or positivity hypothesis, and must not multiply by a
  sentinel factor in a short column.

Implement this in separate audited stages: exact column-cell product,
pointwise path weight, composed equivalence/sum reindexing, and the
determinant equality. Each stage must pass an independent imported
exact-signature/source audit with LeanCert kernel trust before the next
is imported. No `sorry`, `admit`, new axiom, `native_decide`, unsafe
declaration, or per-order enumeration is permitted.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `docs/lean/proofs/MF-03/FINITE_COLUMN_PATH_INVERSE_PRE_REVIEW.md` | `48a482be2235b48f96aad1e4f2f4293f4aa02367e74abc0a1cc179d717f75b2f` |
| `lean-statements/NLA/Proofs/MF03/FiniteColumnPathEquiv.lean` | `fe8c7c82a2d678f791f4df81873d4995b75d1d22a51d72fd68a80d023b3e464e` |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauColumnEquiv.lean` | `aa901f6b28f098a82e3ea4dbde2220350919ab48109559c07198663b835d1a1e` |
| `lean-statements/NLA/Proofs/MF03/FiniteColumnUniformInverse.lean` | `813761d2018fcd3ee8e4e3cdadff0b4a86c8511de1b933cbe1a6bccdaa9e196c` |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauUniformSets.lean` | `88b8122cc8dad90d60a1e1b283bb2d4bd46819a6fc7c9610a7e7a349eaae5575` |
| `lean-statements/NLA/Proofs/MF03/FinitePathWeight.lean` | `5254564d9a0540c284c127dc9ec4f656f4dfa66ba386a5a3faf62937ea0adefe` |
| `lean-statements/NLA/Proofs/MF03/FinitePathEndpoint.lean` | `3e75f71528884e04f9c0e5ace494497b98358652b7e8aec654582c9ddf6aaaed` |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauTail.lean` | `245226b8e05f0aaa15d41a491ec74825a624db02a68a68e6f0741321ef49307d` |
