# Exact TR-06 statement design for independent review

Reviewer/designer: independent AI agent `/root/tr06_statement_referee_2`, 24 September 2026. This is a constructive mathematical and Lean-facing design, not compiled source and not approval of any later Challenge bytes. It adds no hypotheses containing the desired integrability conclusion. No proof bodies are supplied.

## Recommended boundary: metric slope with explicit geometric bridges

The local metric slope is a faithful way to define the angular condition number without constructing a manifold tangent bundle in the public numerical definition. The price is an explicit, proved bridge to the intrinsic derivative in the original question. Proving the slope-integral theorem alone, without the bridges below, should not be advertised as complete TR-06 verification.

### Coordinates, actual rank, and identifiability

Fix `d : ℕ`, `n : Fin d → ℕ`, and `r : ℕ`. Let

```
Index n := (j : Fin d) → Fin (n j)
Tensor 𝕜 n := EuclideanSpace 𝕜 (Index n)
Summands 𝕜 n r := PiLp 2 (fun _ : Fin r => Tensor 𝕜 n)
```

The Frobenius tensor norm and product Frobenius norm are then the existing Hilbert norms. The index set is a dependent product; it has the correct cardinality `∏ j, n j`. It is not a disjoint union of mode indices. Algebraic coordinate maps may use ordinary Pi types internally, but the analytic norms must use these Euclidean structures.

For raw factors `u : (j : Fin d) → Fin (n j) → 𝕜`, define the outer tensor coordinatewise:

```
outer u I = ∏ j, u j (I j).
```

Define `RankOne a` to mean `a ≠ 0 ∧ ∃ u, a = outer u`. This is genuine rank one; zero must not count. Define an ordered `Decomposition r A a` by `(∀ i, RankOne (a i)) ∧ ∑ i, a i = A`. Plain Pi tuples are sufficient for this algebraic predicate.

Avoid a total natural-valued rank definition whose default would need separate justification. Define:

```
ExactRank r A :=
  (∃ a : Fin r → Tensor 𝕜 n, Decomposition r A a) ∧
  ∀ q : ℕ, q < r → ¬ ∃ b : Fin q → Tensor 𝕜 n, Decomposition q A b.
```

The empty decomposition for `q = 0` has sum zero, as required. `Identifiable r A` means an ordered decomposition exists and any two ordered r-term decompositions differ by a permutation in `Equiv.Perm (Fin r)`. Quantify over actual rank-one tensors, not over factor vectors: factor rescaling would otherwise produce infinite fibers even for an identifiable tensor. For the real sampling domain use

```
D := {A : Tensor ℝ n | ExactRank r A ∧ Identifiable r A}.
```

### Nonvacuous generic complex identifiability

A concrete polynomial-witness predicate is appropriate:

```
GenericComplexIdentifiable n r :=
  ∃ p : MvPolynomial (Index n) ℂ,
    (∃ A : Tensor ℂ n, ExactRank r A ∧ eval p A ≠ 0) ∧
    ∀ A : Tensor ℂ n, ExactRank r A → eval p A ≠ 0 → Identifiable r A.
```

Here `eval` is the actual multivariate polynomial evaluation on tensor coordinates. The explicit exact-rank-r witness prevents both the zero-polynomial loophole and the empty-rank-stratum loophole. This is a principal-open formulation of the canonical relative Zariski-generic hypothesis. Prove equivalence with an exceptional algebraic subset proper in the Zariski closure of the complex rank-r locus; do not silently change "proper" into proper in the entire ambient tensor space. A polynomial can be nonzero in the ambient ring and vanish on the entire secant variety.

This formulation does not assert that the real locus is nonempty, regular, or full-dimensional. Those are consequences to prove. In particular, real density in the complex factor-parameter space is needed for a real regular point and hence positivity of the Gaussian normalizer. Also, a real tensor can have complex rank strictly smaller than its real rank. Therefore a real exact-rank-r point is not automatically covered by the polynomial-witness conclusion about complex exact rank r. Prove that the smaller-complex-rank locus has zero k-dimensional induced measure, using the lower secant dimension bound, before applying that conclusion almost everywhere. If a real rank-r decomposition exists and complex exact-rank-r identifiability holds, its unique complex decomposition is necessarily the already existing real one.

The witnessing polynomial need not be homogeneous. Thus `{p ≠ 0}` need not be a cone. Do not use that principal open itself for polar coordinates without an additional argument. Construct the regular cone from scaling-invariant rank/identifiability/smoothness/derivative conditions, or prove that the homogeneous components of a polynomial vanishing on the conic bad set also vanish there and select a useful component.

### Unordered normalized distance

For any ordered tuple `a`, define `normalize a : Summands ℝ n r` by `(normalize a) i = ‖a i‖⁻¹ • a i`. On actual decompositions all denominators are positive.

For `A, B ∈ D`, choose any decompositions `a, b` and set

```
angularDistance A B =
  min_{σ : Equiv.Perm (Fin r)} ‖normalize a - normalize (b ∘ σ)‖.
```

Prove choice independence using identifiability and the permutation linear isometries of `PiLp 2`. A fully choice-free alternative is the real infimum of `‖normalize a - normalize b‖` over every pair of actual decompositions of `A` and `B`; on D prove that this set is finite, nonempty, bounded below, and that the infimum is the displayed finite minimum. Outside D define the distance to be zero, since it is used only on D in the slope.

This is a pseudodistance in A, since positive radial scaling preserves the normalized decomposition. That is intentional. Do not confuse it with the ordinary tensor distance or claim it is a metric on D.

Define a nonnegative extended-valued pointwise slope, using genuine tensor Frobenius distance in the denominator:

```
angularSlope A : ℝ≥0∞ :=
  ⨅ (ε : ℝ) (_ : 0 < ε),
    ⨆ (B : Tensor ℝ n) (_ : B ∈ D)
       (_ : 0 < ‖B - A‖) (_ : ‖B - A‖ < ε),
      ENNReal.ofReal (angularDistance A B / ‖B - A‖).
```

This is the pointwise limsup as B approaches A through D, not the stronger Lipschitz constant comparing all pairs in a neighborhood. The infimum of neighborhood suprema is the relevant derivative norm for a differentiable local branch. Infinite slopes are representable. No Bochner-integral default or `ENNReal.toReal ∞ = 0` is involved.

### Induced volume, density, and complete analytic target

Set

```
k := r * (1 + ∑ j, (n j - 1))
ν := (MeasureTheory.Measure.euclideanHausdorffMeasure k).restrict D
w A := ENNReal.ofReal (Real.exp (-‖A‖ ^ 2 / 2))
Z := ∫⁻ A, w A ∂ν
μ := Z⁻¹ • ν.withDensity w
```

Use normalized Euclidean Hausdorff measure `μHE[k]`, not raw `μH[k]`, for literal correspondence to induced Euclidean volume. Show D is measurable. All k-dimensional measure and manifold claims must use the same dimension k.

The main target can state the conjunction

```
∀ d n r,
  3 ≤ d → (∀ j, 2 ≤ n j) → 3 ≤ r →
  GenericComplexIdentifiable n r →
    0 < Z ∧ Z < ∞ ∧
    AEMeasurable angularSlope ν ∧
    IsProbabilityMeasure μ ∧
    (∫⁻ A, angularSlope A ∂μ) < ∞.
```

Or split the normalizer, measurability, probability, and finite-mean assertions into separately compared public theorems. Include each advertised declaration in Comparator. The only mathematical hypotheses are the canonical dimensions/rank and generic complex identifiability. Finite graph volume, link integrability, regular-locus existence, radial formulas, and normalization are all proof obligations, never structure fields supplied by the caller.

### Mandatory correspondence theorems

1. **Permutation independence.** The normalized tuple orbit and `angularDistance` agree with any chosen local ordering and are invariant under changing the chosen decompositions.
2. **Local slope equals angular derivative.** At every smooth regular identifiable point, and for each legitimate local inverse Ψ of the actual ordered addition map, prove

   `angularSlope A = ENNReal.ofReal ‖D(p^{×r} ∘ Ψ)(A)‖`.

   The norm on the domain is the induced Euclidean tangent norm, and the target norm is `PiLp 2`. If Lean expresses this using a chart `χ : ℝ^k → M`, the correct coordinate quantity is `sup_v ‖D(f ∘ χ) v‖ / ‖Dχ v‖`; a chart-coordinate operator norm alone is generally wrong because the chart need not be an isometry.
3. **Real regular full-measure locus.** From the generic complex hypothesis, construct a scaling-invariant locus `Mreg ⊆ D` of smooth rank-r tensors with finite inverse derivative and show `ν (D \ Mreg) = 0`. Show the rank-one product and addition map have actual local inverses there. Prove the real locus has dimension k and nonempty positive induced volume.
4. **Canonical smooth-locus measure.** Let `S` denote the canonical smooth identifiable real rank-r locus, with induced volume. Show it agrees with `μHE[k]` restricted to S and that S differs from D, and from Mreg, only by a `μHE[k]`-null set. Equivalently define a precise geometric smooth-locus predicate using local embedded-manifold charts, and prove the null-complement theorem for that predicate. It is acceptable to use a standard existing smooth-locus API; it is not acceptable to define "smooth identifiable locus" to mean whatever subset already has the desired integral estimate.
5. **Expectation correspondence.** Combine the previous facts to identify the probability law and nonnegative integral with the canonical density `Z⁻¹ exp(-‖A‖²/2) dV`, independently of values on excluded null sets. This final equality converts the slope target into TR-06, rather than leaving that conversion in prose.

For item 2, finite permutation orbits have a positive gap between distinct normalized orderings at A; continuity of the local branch then makes the quotient distance equal its ordinary Euclidean distance from the chosen normalized tuple for all sufficiently close B. The pointwise slope of a differentiable map on a smooth manifold equals its intrinsic derivative norm, by an upper differentiability bound and tangent curves realizing directions.

Crucial issue: injectivity of the Terracini derivative and uniqueness of one preimage alone do not guarantee that every nearby B in D lies in the local inverse branch. A singular image can have another local branch reached by preimages escaping the chosen source neighborhood. Include smoothness of the secant closure and local image equality / a valid embedded-manifold inverse theorem. The generic full-measure construction must prove those conditions, not assume them globally.

## Alternate explicit tangent-ratio boundary

This can be useful internally, or as a separately proved equivalent definition. It does not avoid the induced-manifold area/volume work.

For a nonzero rank-one tensor a, define `Ta : Submodule ℝ (Tensor ℝ n)` as the span of all one-factor replacements of every factorization of a:

```
outerReplace u j v = outer (Function.update u j v)
Ta = span ℝ {x | ∃ u j v, outer u = a ∧ x = outerReplace u j v}.
```

Dependent `Function.update` needs ordinary implementation care; the mathematical definition is exact. Prove that one chosen nonzero factorization already generates this same space, that it has dimension `1 + sum_j(n_j-1)`, and that it equals the true tangent space of the nonzero rank-one manifold. The all-factorizations span is intrinsic and avoids unproved choice independence in the definition.

For `a : Fin r → Tensor ℝ n`, take the tangent-product Hilbert space

```
Va := PiLp 2 (fun i : Fin r => Ta (a i)).
Sa v := ∑ i, (v i : Tensor ℝ n).
Na v := toLp 2 (fun i =>
  ‖a i‖⁻¹ • (v i : Tensor ℝ n) -
  (inner ℝ (a i) (v i) / ‖a i‖^3) • a i).
```

These are real continuous linear maps. If `Sa` is injective, define

```
tupleAngularCondition a :=
  ⨆ v : Va, ENNReal.ofReal (‖Na v‖ / ‖Sa v‖).
```

At v = 0 both numerator and denominator vanish and the ratio is zero; injectivity prevents any other zero denominator. This supremum equals the operator norm of `Na ∘ (Sa : Va ≃L[ℝ] Sa.range)⁻¹`, whose domain has the induced tensor norm. Existence and continuity of that inverse follow from finite dimensionality. On noninjective `Sa`, set the value to ∞ or explicitly restrict the sampling domain to a proved full-measure regular locus. Simply using real division at zero without an injectivity guard can silently erase singular behavior.

Take the supremum of `tupleAngularCondition a` over actual ordered decompositions of A, or prove permutation invariance and choose one. Prove equality with the metric slope and the original derivative on Mreg. The normalization derivative formula uses the tensor Frobenius inner product, no absolute value in its linear scalar term, and the cubic norm denominator as shown. For complex factors only the identifiability hypothesis is complex; the sampled tangent calculus and normalization derivative are real.

The rank-one tangent-product route is algebraically precise but requires at least as much local manifold correspondence as the metric-slope route. I recommend the metric-slope boundary for compact public definitions, with the tangent-ratio expression as a technical bridge for the derivative and scaling proofs.

## API notes and remaining hard obligations

- `RingTheory/Nullstellensatz.lean` supplies actual multivariate `zeroLocus` and `vanishingIdeal` operations, if the principal-polynomial definition is related to algebraic closure via that API.
- `Analysis/InnerProductSpace/PiL2.lean`, `Analysis/Normed/Lp/PiLp.lean`, and `Analysis/InnerProductSpace/Calculus.lean` supply Euclidean norms, product spaces, and norm-square derivatives. This avoids inventing numerical norms.
- `Geometry/Euclidean/Volume/Measure.lean` supplies `μHE[k]` and normalized affine volume; `Analysis/InnerProductSpace/NormDet.lean` supplies linear Gram volume factors.
- The slope is expected to be semialgebraic in an extended-valued sense because its graph/bounds can be expressed by quantified real polynomial conditions after adding norm variables. Its measurability still must be proved. Choice independence alone does not establish it.
- Neither approach makes semialgebraic projection, finite-dimensional stratification, bounded graph volume, the nonlinear graph area formula, or the conic polar formula disappear. No such complete development was located in the pinned Mathlib source audit.
- Proving only radial integrability or one of the tangent-ratio formulas remains partial progress. Full status and a PR described as fully verified must await all correspondence and geometric obligations, reproducible kernel verification, and permitted-axiom checks.
