# MF-03 finite elementary coefficients: pre-implementation contract

**Author:** `/root`, 10 October 2026. **Status:** awaiting independent mathematical review before Lean implementation. This is Gate 3 of the independently approved all-order Schur–Padé contract, restricted to one coefficient at a time. It does not assert a dual Jacobi–Trudi identity or a determinant limit.

The already frozen exact weights are `a_k=cosineFactor(k+1)=1/[π²(k+1/2)²]>0`. The existing infinite coefficient is

```text
cosineElementaryCoeff j
  = ∑' S : {S : Finset ℕ // S.card=j}, ∏ k∈S.val, a_k.
```

For all `N,j : ℕ`, define the **finite** elementary coefficient by subsets of exactly `Finset.range N`:

```text
finiteCosineElementaryCoeff N j
  = ∑ S ∈ (Finset.range N).powersetCard j, ∏ k∈S, a_k.
```

Prove the exact conclusions for every `j`:

```text
0 ≤ finiteCosineElementaryCoeff N j,
finiteCosineElementaryCoeff N j ≤ finiteCosineElementaryCoeff (N+1) j,
finiteCosineElementaryCoeff N j ≤ cosineElementaryCoeff j,
Tendsto (fun N => finiteCosineElementaryCoeff N j) atTop
  (nhds (cosineElementaryCoeff j)).
```

Every finite subset `S` of cardinality `j` lies in `Finset.range N` for all sufficiently large `N`; the cutoff sets therefore exhaust the exact subtype indexing the infinite coefficient. The product weights are nonnegative, and the full family is summable by the finite-subset product argument from `CosineCoefficientTransfer.lean`. Its summability helper is private, so the implementation may reproduce that generic argument, or prove an equivalent summability lemma, without changing the existing frozen source. The monotone finite sums converge to the full `tsum`; no numerical approximation, altered factor start, or determinant identity is involved.

Edge cases are part of the claim: `j=0` gives 1 for every `N`, including `N=0`; `j>N` gives zero at finite cutoff; and `N=0` has only the empty subset. The existing all-order identity `cosineElementaryCoeff j=1/(2j)!` remains intact. The new theorem must not be presented as a full MF-03 Target proof. Preserve the canonical README, permanent ID, and frozen Lean Target.
