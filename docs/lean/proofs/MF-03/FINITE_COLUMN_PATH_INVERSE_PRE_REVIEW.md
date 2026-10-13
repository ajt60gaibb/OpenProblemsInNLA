# MF-03 exact inverse of finite column labels and valid paths

**Status:** source-locked mathematical and indexing contract for independent
review before implementing either inverse theorem in Lean. This continues the
approved finite cut reconstruction and retains the original MF-03 endpoints,
factor order, augmented shape, and weights.

## Domains and maps

Fix arbitrary natural numbers `N,m,j` with `hj : j ≤ m`. Put
`I = finitePathStart m j hj` and `J = finitePathEnd m`. The two existing maps
are

```text
E : FiniteValidPath m N I J → FiniteColumnSystem N m j
    = finitePathToColumnSystem N m j hj,
C : FiniteColumnSystem N m j → FiniteValidPath m N I J
    = finiteColumnSystemToPath hj.
```

For a column system `D`, write `S_p = D.labels p`, and define
`F_p(q)=|{k∈S_p : q≤k}|` and `P_q(p)=I_p+F_p(q)`. The frozen constructor
`C(D)` is exactly the chain `P_N,P_(N−1),...,P_0`. The first transition
of its length-`n+1` auxiliary chain is `P_(n+1)→P_n` and carries factor
label `n`. All `S_p` consist of labels `<N`; no sentinel label occurs in
`D` or `C(D)`.

## First inverse: recover each entire column set

For `n≤N`, let `C_n(D)` be the frozen `finiteColumnCutPathAux hj D n hn`,
from `P_n` to `P_0`. The exact induction invariant, for each `p : Fin m`, is

```text
finiteAdvanceLabels m n P_n P_0 C_n(D) p
  = {k∈S_p : k<n}.
```

For `n=0`, both sets are empty. For `n+1`, the frozen suffix recurrence
gives `P_n(p)=P_(n+1)(p)+[n∈S_p]`. Thus the first transition advances
coordinate `p` **if and only if** `n∈S_p`. The recursive definition of
`finiteAdvanceLabels` inserts `n` exactly in this case. The remaining
labels are `{k∈S_p:k<n}` by induction; since `n` does not belong to this
set, the resulting set is `{k∈S_p:k<n+1}`. This argument is valid for
`n+1≤N`, with no assumption that `S_p` is nonempty.

At `n=N`, the frozen endpoint transports identify `C_N(D)` with `C(D)`.
Because every `k∈S_p` is `<N`, the filter `{k∈S_p:k<N}` is exactly
`S_p`. Hence the required public first inverse is the literal structure
equality

```text
E(C(D)) = D.
```

Structure extensionality must use equality of `labels p` for every `p`;
proof fields are propositionally irrelevant. Matching only cardinalities
is insufficient.

## Cut extensionality for paths

For arbitrary strict endpoint tuples `X,Z` and two existing
`FiniteValidPath m N X Z` values `c,c'`, prove the following auxiliary
principle by induction on `N`:

```text
(∀ q≤N, finitePathAtCut m N X Z c q
       = finitePathAtCut m N X Z c' q) → c=c'.
```

At `N=0`, a path is a proof of `X=Z`, so equality follows by proof
irrelevance. At `N=n+1`, cut `q=n` is exactly the first intermediate
tuple `Y` of each path, because `n≠n+1`. Cut equality therefore gives
equal first tuples. For every `q≤n`, the definition of
`finitePathAtCut` on a length-`n+1` path reduces to the corresponding
cut of the tail. Apply the induction hypothesis to the two tails;
the `finiteValidStep` fields are proofs and hence proof irrelevant.
This determines the **literal chain**, not just its weight or label
sets.

## Second inverse: recover every intermediate cut

First prove by induction on `n≤N` that for every `q≤n`, the auxiliary
chain `C_n(D)` has cut tuple exactly `P_q`:

```text
finitePathAtCut m n P_n P_0 C_n(D) q = P_q.
```

At `n=0`, this is the starting tuple `P_0`. At `n+1`, cut `q=n+1`
is the starting tuple `P_(n+1)`; every other `q≤n` reduces to the
length-`n` tail. After endpoint transport this yields, for all `q≤N`,

```text
finitePathAtCut m N I J C(D) q = P_q.
```

Now take an original `c : FiniteValidPath m N I J` and set `D=E(c)`.
The frozen `finitePathAtCut_eq_suffix` states coordinatewise that

```text
I_p + |{k∈D.labels p : q≤k}|
  = (finitePathAtCut m N I J c q)_p
```

for every `q≤N` and every `p`. By extensionality of `StrictRows`,
the cut of `c` is `P_q`; by the previous induction, so is the cut of
`C(D)`. Cut extensionality therefore gives the second literal inverse

```text
C(E(c)) = c.
```

Together the two results may be packaged as an `Equiv` between the
unchanged existing types. Its forward map is `E` and inverse map is
`C`; no quotient or relaxed tableau/path type is introduced.

## Boundary and later use

- `m=0`: all coordinate statements are vacuous, but the path cut
  extensionality still proves equality of its stationary empty chains
  for every `N`.
- `N=0,m>0`: the exact domains may be empty by their existing endpoint
  and positive column-cardinality conditions; the inverse laws remain
  universally valid without a separate order enumeration.
- `j=0` and `j=m`: both inverse inductions use only the frozen exact
  endpoints and cardinalities, so they retain the original all-short
  and all-long shapes.
- Neither inverse inserts the sentinel `N` or evaluates any
  `cosineFactor`. Weight transport and the finite determinant/tableau
  sum identity are later separate gates.

Implementation should use new modules for the two inverse directions
and final equivalence, each direct checked and then independently
audited at its exact imported signature with LeanCert kernel trust.
There is no per-order enumeration, `sorry`, `admit`, new axiom,
`native_decide`, or unsafe declaration.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `docs/lean/proofs/MF-03/FINITE_COLUMN_CUT_RECONSTRUCTION_PRE_REVIEW.md` | `e765a2f2047ec10619a5b37fd7bbaf7ab26f3167fb2872183cb278fd44779ff8` |
| `lean-statements/NLA/Proofs/MF03/FinitePathLabels.lean` | `03a60687fa2ffa5c6a87857bd541b70256276b138951a58fac9979b5e8c09b60` |
| `lean-statements/NLA/Proofs/MF03/FinitePathCuts.lean` | `40332d778cd3b352fab350a256b8afa801c7cf699fc391ca720f3d3519295c7a` |
| `lean-statements/NLA/Proofs/MF03/FiniteColumnSystem.lean` | `9cc6088edfafd3d23b028cd15419a21ff83cab21b6e898b8488159c0195eacb9` |
| `lean-statements/NLA/Proofs/MF03/FiniteColumnCutEndpoints.lean` | `ae23b248556bd85aaefc6512639c2e1ac3a7e8be369b913cbb42228f6f475bfe` |
| `lean-statements/NLA/Proofs/MF03/FiniteColumnCutPath.lean` | `f292db6d7750c4359f4d0020b7afcacef0ad25dd40f026efe0a7335a520bbcbb` |
