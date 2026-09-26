# TR-06 exact statement design without a manifold-measure prerequisite

Independent design review by `/root/tr06_statement_referee_1` (AI), 24 September 2026.
This is a design document, not compiled Lean and not approval of a formalization. No proof bodies are proposed. Pinned API source inspected: Mathlib commit specified by parent, `0df444a…`, at `/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.lake/packages/mathlib`.

## Recommendation

Use the parent's metric-local-slope proposal for the public numerical quantity. It is coordinate-free, requires no arbitrary global labeling, and does not invoke an ambient derivative which silently defaults to zero. Use ambient Hausdorff measure of the correct intrinsic dimension restricted to the set of all real identifiable rank-r tensors. The final Challenge must also demand proved local derivative correspondence and a null-complement regular-locus bridge. Without these bridges it is not yet a complete verification of the canonical derivative/induced-volume target.

The explicit tangent-span alternative below can provide a convenient intermediate linear-algebra expression, but does not remove the required geometry and measure proof.

## Concrete mathematical definitions, directly expressible in Lean

For `d : ℕ`, `n : Fin d → ℕ`, let:

```lean
abbrev TensorIndex (n : Fin d → ℕ) := (j : Fin d) → Fin (n j)
abbrev Tensor (𝕜 : Type*) [RCLike 𝕜] (n : Fin d → ℕ) :=
  EuclideanSpace 𝕜 (TensorIndex n)
abbrev Summands (𝕜 : Type*) [RCLike 𝕜] (n : Fin d → ℕ) (r : ℕ) :=
  Fin r → Tensor 𝕜 n
abbrev SummandOutput (n : Fin d → ℕ) (r : ℕ) :=
  PiLp 2 (fun _ : Fin r => Tensor ℝ n)
```

`EuclideanSpace` is genuinely l2 by the inspected `Mathlib/Analysis/InnerProductSpace/PiL2.lean`. Never use the default Pi norm on `Summands` as the output Frobenius norm; either convert to `SummandOutput`, flatten into `EuclideanSpace ℝ (Fin r × TensorIndex n)`, or explicitly take `sqrt (∑ i, ‖a i‖^2)`.

1. `RankOne a` means `a ≠ 0` and there exist factors `v : (j : Fin d) → Fin (n j) → 𝕜` such that `∀ q, a q = ∏ j, v j (q j)`.
2. `IsDecomposition r A a` means `(∀ i, RankOne (a i)) ∧ (∑ i, a i = A)`.
3. `HasDecomposition r A` is the existential closure over a.
4. `ExactRank r A` means `HasDecomposition r A ∧ ∀ s, s < r → ¬ HasDecomposition s A`. In particular `r=0` behaves normally; no total rank-choice function or upper bound theorem is needed for this definition.
5. `Identifiable r A` means `ExactRank r A` and for all length-r decompositions a,b of A there is `σ : Equiv.Perm (Fin r)` with `∀ i, a i = b (σ i)`.
6. `GenericComplexIdentifiable n r` is the following genuine polynomial exceptional-set predicate, with `A` ranging over `Tensor ℂ n`:

```lean
∃ p : MvPolynomial (TensorIndex n) ℂ,
  (∃ A, ExactRank r A ∧ MvPolynomial.eval (fun q => A q) p ≠ 0) ∧
  ∀ A, ExactRank r A → MvPolynomial.eval (fun q => A q) p ≠ 0 →
    Identifiable r A
```

The witness excludes a polynomial vanishing on the entire rank-r locus; merely asking `p ≠ 0` would NOT exclude that vacuity. Conversely, any proper algebraic exceptional set of the secant variety is contained in the zero set of a polynomial which is not identically zero there. Prove the equivalence with the canonical generic condition using irreducibility/density of the rank-r secant image; do not simply claim the witness establishes density for arbitrary reducible sets. No integrability, finite volume, regular locus, inverse map, derivative bound, or measure property occurs in this predicate.

7. `S n r : Set (Tensor ℝ n) := {A | Identifiable r A}`.
8. `k n r : ℕ := r * (1 + ∑ j, (n j - 1))`. Under `d>=3`, every `n j>=2`, `r>=3`, prove `1 < k n r`.
9. `normalize a i := ‖a i‖⁻¹ • a i`; all summands in a decomposition are nonzero. This scalar normalization precedes every derivative or metric difference.
10. For actual decompositions a of A and b of B define

`D(a,b) = min_{σ ∈ S_r} sqrt(∑ i, ‖normalize a i - normalize b (σ i)‖²)`.

Use an ENNReal infimum over the finite nonempty permutation group if avoiding `Finset.min'` proof plumbing. Prove `D` is unchanged by any relabeling of either tuple. On identifiable A,B it is independent of the chosen decompositions.

A completely choice-free definition is

`angularDistance A B = inf_{a : Decomp(A)} inf_{b : Decomp(B)} inf_{σ∈S_r} ofReal(sqrt(∑i, ‖normalize a i - normalize b(σ i)‖²))`.

The infimum over an empty decomposition type is top, but A,B used by the slope lie in S and therefore the types are nonempty. Prove reduction to the finite permutation minimum for any two chosen decompositions. This is a pseudodistance: it can vanish for distinct tensors on the same positive ray, exactly as desired for angular normalization.

11. With ENNReal numerator and denominator define for EVERY A:

```text
angularSlope(A) = inf_{ε : ℝ, 0<ε}
  sup_{B ∈ S, 0<dist(A,B), dist(A,B)<ε}
    angularDistance(A,B) / ENNReal.ofReal(dist(A,B)).
```

The puncture condition is essential. Supremum over an empty neighbor set is zero; this convention does not affect the eventual regular locus. Restricting the neighbor set to S is correct only once S locally agrees with the smooth image manifold at regular points. The quantity can be infinity at exceptional points. Never replace it by `.toReal` before proving almost-everywhere finiteness/integrability.

12. Define `ν := (MeasureTheory.Measure.hausdorffMeasure (k n r : ℝ)).restrict (S n r)` on the ambient Euclidean tensor space. Mathlib's Hausdorff measure in `Measure/Hausdorff.lean` is `mkMetric (fun radius => radius ^ dim)`: its normalization is not the usual Euclidean Riemannian normalization in general dimensions. The two differ by a fixed positive finite dimension-dependent constant on smooth k-manifolds; cancellation in the normalized probability law must be justified.
13. `w A := ENNReal.ofReal (Real.exp (-(‖A‖^2)/2))`.
14. `Z := ∫⁻ A, w A ∂ν` in ENNReal, then `μ := Z⁻¹ • (ν.withDensity w)`.

## Required full Challenge conclusions

The sole mathematical assumptions of the universal final theorem are the format inequalities and `GenericComplexIdentifiable n r`. A useful explicit theorem output is:

```text
MeasurableSet (S n r)
∧ AEMeasurable (angularSlope n r) ν
∧ 0 < Z n r
∧ Z n r < ∞
∧ μ n r Set.univ = 1
∧ (∫⁻ A, angularSlope n r A ∂μ n r) < ∞.
```

Measurability should be explicit or separately proved. A bare lintegral is not a substitute for proving that the random quantity is measurable. The normalized measure and density are definitional data, not parameters supplied by the theorem caller.

These conclusions are not sufficient by themselves for canonical status promotion unless the following correspondence theorems are also proved and included in the reviewed Challenge dependency set.

## Mandatory correspondence theorems

### A. Permutation minimum and local smooth branch

At a minimal decomposition no two summands are proportional. Thus normalized summands are pairwise distinct and every nonidentity permutation has strictly positive displacement at A. Given a continuous local branch, the identity permutation uniquely minimizes the angular distance to the base branch for all sufficiently near points. This is where finite-group minimum becomes the ordinary norm of a local smooth map. It also proves independence of labeling.

### B. Local chart slope equals induced tangent derivative norm

State a GENERAL local-chart theorem using only open subsets of finite-dimensional Euclidean spaces. Let `U ⊂ ℝ^k` be open, `u0∈U`, `φ : ℝ^k → E` C1 on U, and `a : ℝ^k → SummandOutput` a C1 decomposition branch on U. Require:

- `φ u0=A`;
- a neighborhood `O` of A satisfies `φ '' U = S ∩ O` after shrinking charts;
- `φ|U` has a continuous inverse on `S∩O` (express as `BijOn`, `ContinuousOn`, and explicit left/right inverse data if avoiding manifold APIs);
- `Dφ(u0)` is injective;
- for all `u∈U`, `a(u)` is an actual ordered decomposition of `φ(u)`.

Then prove

```text
angularSlope A =
  sup_{v ≠ 0} ofReal(‖D(normalize ∘ a)(u0)[v]‖)
                / ofReal(‖Dφ(u0)[v]‖).
```

This quotient is exactly the operator norm of the map on the induced tangent subspace `range Dφ` given by `D(normalize∘a) ∘ (Dφ)⁻¹`. An optional second theorem constructs that continuous linear map and identifies its norm with the quotient. This statement uses the Frobenius norm of the embedded input direction, not the norm of the parameter vector. No orthonormal chart is assumed.

The chart lemma is local calculus and does not require any semialgebraic assumptions. Proving it involves local first-order expansion, a positive lower bound for an injective finite-dimensional linear map, and paths `u0+t*v` inside U. The inverse-chart continuity transfers ambient B→A to coordinate u→u0.

### C. Full-measure existence of such charts

From ONLY `GenericComplexIdentifiable` and the format bounds, construct a Borel/semialgebraic cone `R ⊂ S`, show `ν (S \ R)=0`, and show every A∈R has the charts in B with the expected dimension k. Also show nonemptiness. This requires the generic algebraic geometry and real Zariski-density facts from the source proof. It cannot be a hypothesis to the final theorem or an unproved field in a supplied model.

The chart neighborhood condition must be equality with S locally, not merely an immersed chart image contained in S: otherwise the slope may see additional approaches not represented by the chart. The smooth secant-image locus plus identifiability and regularity of ordered addition supplies the required local equality.

### D. Canonical domain and measure equivalence

Prove that the canonical smooth identifiable locus and R differ only by a k-dimensional Hausdorff-null set. Prove induced-volume measure is a fixed positive finite multiple of ν on the regular charts. It follows that normalized Gaussian laws agree after null-set removal. Combine B with permutation independence to identify angularSlope with `‖D(p^r ∘ Ψ)‖` almost everywhere. This is the promised correspondence to the original statement, not an optional explanatory comment.

If the project intentionally avoids naming a manifold/Riemannian-volume object, a fully explicit chart-based induced-volume construction with change-of-chart invariance can serve as the formal definition of the canonical measure. The identification theorem then relates that explicit induced-volume construction to Hausdorff measure. This is considerable additional work; a prose claim alone must not be described as complete formal correspondence.

## Optional explicit tangent intermediate

For rank-one a, define its tangent subspace as the span of all tensors obtained by replacing one factor in any factor representation of a with an arbitrary vector, retaining the other factors. Prove independence of factor representation and dimension `1+sum(n_j-1)`.

For an ordered tuple a, its product tangent consists of tuples v with each `v_i` in the corresponding rank-one tangent. The tangent addition map is `v ↦ Σ_i v_i`.

The componentwise normalized derivative is the explicit real-linear map

`N_a(v)_i = (v_i - (⟪a_i,v_i⟫ / ‖a_i‖²) • a_i) / ‖a_i‖`.

On a regular decomposition (injective tangent addition), define

`K(a) = sup_{v≠0 in product tangent} ‖N_a(v)‖ / ‖Σ_i v_i‖`.

Its finiteness follows from finite-dimensional injectivity, and it is exactly the derivative norm in B after proving the Segre tangent theorem and normalization derivative. This can avoid constructing inverse continuous-linear maps and helps expose the correct norms. It is a derived characterization of angularSlope on R, not a replacement with an unproved correspondence.

## Remaining substantive proof burden

This design permits a nonvacuous complete statement using existing foundational types. It does NOT make the source proof cheap: semialgebraic projection/stratification/dimension, bounded semialgebraic finite volume, generic complex-to-real regular-locus construction, graph area comparison, and cone polar integration still require kernel proofs. A partial finite-dimensional or radial lemma must remain labelled partial. No LeanCert scalar certificate can stand in for these theorems.
