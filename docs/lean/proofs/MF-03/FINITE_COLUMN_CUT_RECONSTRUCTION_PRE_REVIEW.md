# MF-03 literal path reconstruction from finite column labels

**Status:** exact mathematical and indexing precontract for independent
review before direct Lean checking of the new path-reconstruction gates.
It refines the independently approved
`FINITE_UNIFORM_SENTINEL_PRE_REVIEW.md` without changing the original
MF-03 problem, endpoints, tableau shape, or factor coefficients.

## Inputs and original indexing

Fix arbitrary `N,m,j : ℕ` with `j ≤ m` and
`D : FiniteColumnSystem N m j`. For `p : Fin m`, write `S_p = D.labels p`.
Every `k ∈ S_p` satisfies `k < N`. The exact cardinality is `m+1` for
`p<j` and `m` for `p≥j`. At every cut `q≤N` and adjacent `p,p+1`, the
source-locked condition is

```text
|{k∈S_p : q≤k}| ≤ |{k∈S_(p+1) : q≤k}| + [p+1=j].
```

The original starting positions are
`I_p = p` if `p<j`, and `I_p=p+1` if `p≥j`. The terminal positions are
`J_p=m+1+p`, both in `Fin(2m+1)`. In particular,
`I_(p+1)-I_p = 1+[p+1=j]` at adjacent positions and
`J_p-I_p = |S_p|`. These are the original row/column indices of the
finite augmented determinant; they are not reordered.

## Exact finite-cut arithmetic

For a finite set `S⊆ℕ`, define `F_S(q)=|{k∈S:q≤k}|`. The next gate must
prove the exact identities

```text
F_S(0)=|S|,
F_S(N)=0                    if every k∈S satisfies k<N,
F_S(q)=F_S(q+1)+[q∈S]      for every q∈ℕ.
```

The last identity counts a label at the zero-based factor index `q`.
No finite-factor product or tableau coefficient is changed.

## Cut positions and strict ordering

For each cut `q≤N`, set

```text
P_q(p) = I_p + F_(S_p)(q).
```

The Lean construction must prove `P_q(p)<2m+1` from
`F_(S_p)(q)≤|S_p|=J_p-I_p`, hence `P_q(p)≤J_p≤2m`. It must package
`p↦P_q(p)` as the existing `StrictRows m`, not as a relaxed position
type. For each adjacent pair, the displayed source condition and
`I_(p+1)-I_p=1+[p+1=j]` give `P_q(p)<P_q(p+1)`; transitivity gives
strict ordering for every `p<p'`. The proof must hold uniformly for
all cuts and all `N,m,j` satisfying `j≤m`.

## Endpoints and transition direction

Because actual labels are `<N`, `P_N=I`. Because `F_(S_p)(0)=|S_p|`
and the cardinality equals the endpoint displacement, `P_0=J`.
For every `q` with `q+1≤N`, the recurrence above gives

```text
P_q(p) = P_(q+1)(p) + [q∈S_p].
```

Thus `P_(q+1)→P_q` is an existing `finiteValidStep m`: each coordinate
stays or advances exactly one site, advancing precisely when `q∈S_p`.
Its factor label is **q**. A length-`N` chain is assembled as
`P_N,P_(N−1),...,P_0`; the first transition of a length-`n+1` tail
is `P_(n+1)→P_n` and carries factor label `n`. This is the order in
the existing `FiniteValidPath` and `finiteValidPathWeight` definitions.

## Exact inverse obligations after construction

The reconstructed chain must have advance-label set exactly `S_p` for
every `p`, not merely a matching count. At each cut, its position is
`P_q`; the frozen `finitePathAtCut_eq_suffix` identifies its extracted
label suffix counts with `F_(S_p)(q)`. Equality at `q` and `q+1`, with
the displayed recurrence, determines membership of each `q<N` and
therefore equality of the finite sets.

For an existing valid chain `c`, the frozen cut-position theorem says
its position at every `q≤N` is `I_p+F_(S_p)(q)`. Reconstructing from
its extracted labels must reproduce every intermediate `StrictRows`.
Induction on the chain length, using the cut at its first factor label,
then proves equality of literal `FiniteValidPath` values. These two
identities give the required equivalence between existing valid chains
with the original endpoints and `FiniteColumnSystem N m j`.

Only after that equivalence is kernel checked may the already audited
tableau/column-system equivalence transport weights. The path weight is
the frozen product of `cosineFactor(k+1)` over the actual `S_p`.
Sentinel `N` is absent from those sets and from all cells of
`finiteAugShape m j`; no factor `cosineFactor(N+1)` may appear. The
eventual weighted-sum equality must use these mutual inverses and the
original finite determinant/tableau definitions for every order.

## Boundary cases and implementation gates

- `m=0`: there are no columns or path coordinates; the unique empty
  chain exists for every `N` and has weight `1`.
- `N=0,m>0`: a column system or bounded augmented tableau would require
  positive cardinality from the empty label range, so those domains are
  empty. No order-specific enumeration is used.
- `j=0` and `j=m`: the same cut formula applies with, respectively, no
  long columns or no short columns.

The source-only Lean drafts are split into
`FiniteLabelSuffixStep`, `FiniteColumnCutPositions`,
`FiniteColumnCutEndpoints`, and `FiniteColumnCutPath`. Each is to be
direct checked and frozen only after independent approval of this
contract, then separately audited with exact imported signatures and
LeanCert kernel trust. Later inverse and weighted-sum gates remain
separate. No `sorry`, `admit`, new axiom, `native_decide`, unsafe
declaration, or per-order computation is permitted.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `docs/lean/proofs/MF-03/FINITE_UNIFORM_SENTINEL_PRE_REVIEW.md` | `8d4bbb46364fbe7ad1eef7d85639fe1c54a4186f97a9d8dc22abac87f2c244d9` |
| `lean-statements/NLA/Proofs/MF03/FiniteColumnSystem.lean` | `9cc6088edfafd3d23b028cd15419a21ff83cab21b6e898b8488159c0195eacb9` |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauColumnEquiv.lean` | `aa901f6b28f098a82e3ea4dbde2220350919ab48109559c07198663b835d1a1e` |
