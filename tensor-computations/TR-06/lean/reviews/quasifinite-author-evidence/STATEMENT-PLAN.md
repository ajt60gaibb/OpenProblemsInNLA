# Uniform quasi-finite character count: exact proposed boundary

The typechecked, universe-polymorphic boundary is `/private/tmp/tr06-proof-area/proposals/QuasiFiniteCharactersBoundary.lean`, SHA256 `90fbd3a5d72f961aa31b5e3198c851e3e81aa1034141bdfaca05ea49e995457a`. It contains proposition definitions only, and no theorem asserting them. Implementation awaits independent root approval.

Let R,S be commutative rings, S a finite-type R-algebra, Spec(S) a Noetherian topological space, and K a fixed field. Proposed conclusion:

> There is a natural number B such that, for every R-algebra action on K and every finite subset q of R-algebra homomorphisms S→K whose actual prime kernels are quasi-finite over R, card(q)≤B.

The bound precedes the quantifier over the target algebra action. Characters are not assumed surjective onto K. Kernels are packaged by the explicit definition `characterPrime f := ⟨RingHom.ker f.toRingHom, RingHom.ker_isPrime f.toRingHom⟩`; no geometric or finite-fiber premise is hidden in this definition. No Noetherian hypothesis on R itself is introduced.

## Smaller local statement

For A⊆S an R-subalgebra and r∈A, if `Localization.awayMap A.val.toRingHom r` is surjective, restriction of characters S→K to A is injective on characters satisfying f(r)≠0. This uses only surjectivity, which is supplied by Zariski Main's stronger bijectivity conclusion.

The pinned `Localization.awayMap_surjective_iff` gives the especially simple exact denominator-clearing statement

```
∀ s : S, ∃ b : A, ∃ n : Nat, b.val = r.val^n * s.
```

Thus if f,g have equal restrictions and nonzero value at r, applying them to this equation gives `f(r)^n*f(s)=g(r)^n*g(s)`. Their r-values agree and are nonzero, so cancellation gives f(s)=g(s). It is unnecessary to construct localization lifts or an algebra equivalence for this local character lemma.

## Checked pinned APIs

The exact signatures are retained in the successful `proposals.QuasiFiniteAPIProbe` log under `/private/tmp/tr06-proof-area/evidence/`. Pin: Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

- `Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective` (`RingTheory/ZariskisMainTheorem.lean:703`) actually accepts `[WeaklyQuasiFiniteAt R p]`, supplied by QuasiFiniteAt. With finite type, it produces A⊆S with A.toSubmodule.FG and r∈A outside p, with the localization map bijective. No Noetherian R hypothesis is required.
- `Localization.awayMap_surjective_iff` (`RingTheory/Localization/Away/Basic.lean:506`) gives the displayed denominator identity.
- `Submodule.fg_top` converts A.toSubmodule.FG to finite generation of top in A; `Module.Finite.exists_fin` then gives a finite generating family `Fin N→A` with span top.
- `TopologicalSpace.NoetherianSpace.isCompact` (`Topology/NoetherianSpace.lean:65`) applies to every subset of Spec(S). We can directly use the subset of quasi-finite primes, without separately proving the quasi-finite locus open.
- `PrimeSpectrum.basicOpen`, `mem_basicOpen`, `isOpen_basicOpen` encode the neighborhoods r∉p.
- `IsCompact.elim_finite_subcover` selects finitely many local finite envelopes.
- `Finset.card_image_of_injOn` transfers the finite restricted-character bound to each local subset; `Finset.card_biUnion_le` combines the finite cover bounds.

The existing Zariski Main theorem and denominator lemma both print exactly the standard-three axiom closure. This is an API/trust probe, not a new theorem proof or a tensor-fiber result.

## Assembly plan

1. For every quasi-finite prime p of S, choose the Zariski Main finite envelope A_p and denominator r_p. The corresponding basic open contains p.
2. Compactness of the quasi-finite-prime subset gives a finite collection I of these opens covering it. Each chosen A_i has a finite module-generating family of size N_i. These choices happen before any target R-algebra structure on K.
3. Choose B=∑_{i∈I}N_i.
4. For an arbitrary target action and finite q, filter q by f(r_i)≠0. The local restriction lemma injects each filter into a finite subset of Hom_R(A_i,K).
5. Apply the root's proved `card_algHom_finset_le_of_span_eq_top` in `/private/tmp/tr06-proof-root/NLA/TR06/AlgebraFiber.lean` to bound each filter by N_i. That theorem uses character linear independence and evaluation on generators, with no freeness assumption.
6. Every f∈q belongs to a filter, because its prime kernel is in the finite basic-open cover. Finite-union cardinality gives card(q)≤B.

Potential implementation details are scalar-tower/typeclass bookkeeping for the subalgebras and making target-action binders local instances. These are not missing mathematical hypotheses.

## Scope limit

Even if completed, this theorem only bounds algebraic characters on the quasi-finite locus. It does not construct the tensor source coordinate algebra, prove that normalized tensor graph points inject into such characters, prove analytic local projection injectivity implies algebraic quasi-finiteness at those points, or restore exceptional sets. Those remain distinct obligations, and the bounded graph's fiber theorem D is not automatically proved by this intermediate result.
