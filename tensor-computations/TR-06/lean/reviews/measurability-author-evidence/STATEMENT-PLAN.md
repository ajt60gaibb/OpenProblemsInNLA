# Proposed measurable tensor-locus lemma

Authoring agent: `/root/tr06_statement_referee_2`, for George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Original TR-06 mathematical proof remains attributed to Matthew J. Colbrook. This is a proposed supporting proof route; implementation awaits independent review of this exact boundary.

The exact proposed theorem is:

```lean
theorem measurableSet_identifiableRealSet (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    MeasurableSet (NLA.TR06.identifiableRealSet d n r)
```

There are no mathematical hypotheses. All mode and summand indices are finite, so the result remains true for degenerate dimensions and ranks. It directly proves the first measurability conclusion of the frozen `regular_locus` target when specialized to the canonical range. It does not assert a dimension formula, a regular full-measure locus, finite Hausdorff measure, or integrability.

Let the raw factor-parameter space be

```
Factors d n r := (i : Fin r) → (j : Fin d) → Fin (n j) → ℝ.
tuple u i := pureTensor (u i).
sum u := ∑ i, tuple u i.
U := {u | ∀ i, tuple u i ≠ 0}.
```

Raw parameter spaces may use ordinary Pi norms: only their Euclidean topology matters here. The tensor output remains the frozen Frobenius EuclideanSpace. Each `tuple` and `sum` map is continuous by finite coordinate products and sums. U is open because it is a finite intersection of inverse images of complements of singleton zero. It is sigma compact since the finite-dimensional real parameter space is locally compact and second countable. Its image under `sum` is sigma compact and hence Borel in the Hausdorff tensor space. Prove explicitly that this image equals

```
decomposableSet r := {A | ∃ a : Fin r → Tensor ℝ d n, Decomposes a A}.
```

The frozen `RankOne` includes nonzeroness and actual factorization, so the image equality holds in both directions by selecting factor witnesses for finitely many summands. The empty r = 0 tuple yields the singleton zero, correctly.

The exact-rank set is `decomposableSet r \ ⋃ m < r, decomposableSet m`, hence Borel. No natural-valued rank function or default rank is introduced.

For nonidentifiability, use pairs of raw parameter tuples and set

```
V := {(u,v) | u ∈ U ∧ v ∈ U ∧
       ∀ σ : Equiv.Perm (Fin r), ¬ ∀ i, tuple v i = tuple u (σ i)}.
C := {(u,v) | sum u = sum v}.
```

V is open: each permutation-agreement condition is a finite intersection of closed tensor-coordinate equalities, its complement is open, and the permutation type is finite. C is closed. Therefore C ∩ V is sigma compact (intersect the sigma-compact open set V with the closed set C). Its continuous image under `(u,v) ↦ sum u` is sigma compact and Borel. Prove explicitly that this image equals `{A | ¬ Identifiable r A}`: negating the frozen universal uniqueness assertion gives two actual decompositions not related by any permutation, and factor witnesses recover the parameter pair.

Finally, `identifiableRealSet d n r` is the exact-rank set minus this nonidentifiable image, hence Borel. The fact that `Identifiable r A` is vacuous when no decomposition exists causes no problem: its negation supplies two decompositions, while the final sampling domain explicitly also requires exact rank.

All uses of sigma compactness concern finite-dimensional parameter spaces or continuous images of sigma-compact subsets. The argument does not use the false general claim that arbitrary Borel images are Borel. Nor does it equate parameter-space Lebesgue nullity with induced tensor-volume nullity. It avoids real quantifier elimination for this measurability lemma only; the deeper semialgebraic dimension/finite-volume and regularity steps remain outstanding.
