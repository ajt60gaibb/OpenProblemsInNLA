# TR-06 draft statement review — referee 2

Date: 24 September 2026. Reviewer: independent AI agent `/root/tr06_statement_referee_2`. Phase: pre-proof semantic review of actual definitions and Challenge signatures. Verdict: **REQUEST CHANGES for complete-original-target approval**. The concrete model is substantially faithful, and no mathematically false assertion was found among the five candidate signatures. The requests below concern the remaining original-statement correspondence, which the draft itself identifies as mandatory but does not yet express in compared signatures.

I inspected source, not existing PASS reports. I supplied an earlier design memo; I did not implement these candidate files. I have not independently run Lean on this draft, inspected its elaboration logs, or run Comparator/kernel/axiom checks. There are five deliberate `sorry` placeholders and no proof approval is asserted.

## Exact reviewed bytes

The reviewed files were copied to `draft-reviewed-source/` before writing this report. Machine-readable hashes are in `draft-statement-hashes.json`.

| File under `/private/tmp/tr06-preparation/` | SHA-256 |
|---|---|
| `NLA/TR06/Definitions.lean` | `3e73af048a749d1592677ca4f611fbc6784c506a27724c0cf886a3a52bd49712` |
| `Challenge.lean` | `b5a0d73fb544064c77d9fb102851758177fff3b42a06777a12249ac1d7cdd012` |
| `NUMERICAL_TARGETS.md` | `985a80f78083e40e9f9b440591b848fb9c1786d9de7cc22d004b8a06c184a271` |
| `README.md` | `ec2f48fcd96d35ba256264df08e04b88a0faea6512cfe0b4299f497a681b8021` |

The immutable canonical and manuscript hashes are as recorded in my `source-hashes.json`; they match the draft inventory.

## Definitions and signatures found faithful

- `TensorIndex` is the dependent product of all mode indices; `Tensor` and flattened `AngularOutput` are genuine Euclidean spaces. The norms are Frobenius and product l2, respectively.
- `RankOne` excludes zero and uses actual tensor coordinates. `Decomposes` has exactly r nonzero rank-one summands. `ExactRank` rules out every shorter decomposition, including the empty zero decomposition.
- `Identifiable` by itself omits existence, but every use relevant to the public model is conjoined with `ExactRank` or guarded by exact rank. Thus it does not introduce a vacuity bug here.
- The generic-complex polynomial witness is explicitly nonzero at an actual complex exact-rank-r tensor. This correctly prevents a polynomial vanishing on the whole secant locus from satisfying the hypothesis. The hypothesis contains no integrability or real-regularity assumption.
- `angularDistance` uses an ENNReal infimum over all ordered decompositions. Empty proof-index fibers contribute top; on the sampling domain actual decompositions exist, and identifiability reduces the set to a finite permutation orbit. It is correct that distance outside this domain need not be a finite metric.
- `angularSlope` is the correct infimum of neighborhood suprema. `B ≠ A` makes its edistance denominator positive and finite. It measures variation against the ambient Frobenius distance and preserves radial invariance of the numerator.
- `derivativeRatio` uses real division but every intended application has an injective input differential. Then the only zero denominator is the zero vector, which contributes zero and causes no error. `inducedDerivative` inverts the chart differential onto its actual range and uses the induced subspace norm.
- The chart target is open in the entire identifiable real set. This correctly rules out the omitted-sheet loophole that would remain for an arbitrary immersed patch.
- `induced_volume_chart` is a genuine nonlinear area formula using the Gram volume factor. It is not being substituted by the existing linear-map theorem.
- All measures use normalized Euclidean Hausdorff measure in the expected dimension. The density, mass, reciprocal normalization, positivity, finiteness, and probability assertion are explicit. The final expectations are ENNReal integrals, so real-integral default values cannot satisfy the target.
- `regular_locus` and `finite_angular_mean` do not take the desired finite graph volume, link estimate, or cone geometry as hypotheses. Their present assumptions are the intended dimensions/rank and generic complex identifiability.
- Source attribution, George Stepaniants's name/affiliation, absence of a new contact email, and truthful incomplete status are appropriate.

## Requested change R2-1: close the generic-assumption equivalence in the formal interface

Affected declaration: `Definitions.lean`, `GenericComplexIdentifiable`; affected documentation: the numerical inventory explicitly says equivalence to the original proper-algebraic-exception formulation is a semantic proof obligation. None of the five Challenge signatures discharges it.

The proposed predicate is mathematically equivalent to the original generic assumption; I do not object to its principal-polynomial form. But leaving this conversion only in prose fails the stated requirement that all original-target bridges be formally proved. Add one explicit compared equivalence theorem, or replace the hypothesis with a literal algebraic-exception predicate and prove the polynomial characterization internally.

A compact exact design needs no scheme machinery. Define, by actual `MvPolynomial.eval`, the algebraic hull of `S = {A : Tensor ℂ d n | ExactRank r A}` as

```
algHull S = {A | ∀ p, (∀ B ∈ S, eval p B = 0) → eval p A = 0}.
zeros P = {A | ∀ p ∈ P, eval p A = 0}.
```

Define the original predicate by existence of a set of polynomials P such that

```
(algHull S \ zeros P).Nonempty ∧
∀ A ∈ S, A ∉ zeros P → Identifiable r A.
```

Then the required signature is exactly

```
genericComplexIdentifiable_iff_algebraicException :
  GenericComplexIdentifiable d n r ↔ AlgebraicExceptionIdentifiable d n r.
```

This theorem is elementary from the definitions: a proper zero set supplies one polynomial not vanishing at a hull point, and the hull definition supplies a nonzero evaluation already on S. Conversely use `{p}`. No analytic conclusion, irreducibility assumption, or improper ambient exceptional-set convention is required.

## Requested change R2-2: compare a literal canonical derivative/measure target, not only the surrogate target

Affected declarations: `DecompositionChart`, `regularSet`, `angularSlope_eq_chart_derivative`, `derivativeRatio_eq_operatorNorm`, and `finite_angular_mean`.

The five signatures establish, once proved, a very strong result for an explicitly defined C1 chart model. They do not yet state either (a) that the range-norm operator is the differential of an actual local inverse of ordered rank-one addition, or (b) that the chart-regular Gaussian law is the law on the original smooth identifiable locus. The numerical inventory calls both conversions mandatory and unresolved. Accordingly I cannot presently approve these exact bytes as the complete original-target interface.

This is not an assertion that the C1 construction is mathematically wrong. A C1 embedded chart with a C1 ordered section and injective differential is adequate for all first-derivative and area arguments. The missing point is explicit formal correspondence to the independently stated canonical objects, rather than another relabeling of the same surrogate definitions.

A concrete route to close the boundary is:

1. **Smooth-locus definition.** Add a `SmoothIdentifiableChart` consisting of the same partial homeomorphism into D, an injective ambient differential, and `ContDiffOn ℝ ∞` for its ambient input map, without requiring any decomposition selection. Define the canonical smooth locus S as the union of these chart targets. Use this separate literal geometric definition for canonical volume. Let canonical `DecompositionChart` extend it with smooth ordered summands. The current C1 structure can remain an internal helper, but its fields should not be described as C∞ smooth without a bridge. Prove `regularSet ⊆ S ⊆ D` and that the complement of the regular set in S and in D is null. Full measure of a C1-chart locus alone does not formally state full measure of the C∞ smooth locus.
2. **Actual local branch/inverse.** Define the space of ordered r-tuples of nonzero rank-one tensors, with its Euclidean product topology and the actual summation map Φ. For each decomposition chart and point u in its source, state existence of a local inverse of Φ at the tuple `c.summands u` whose values on a sufficiently small target neighborhood agree with `c.summands ∘ c.chart.symm`. A precise topological version is an `OpenPartialHomeomorph` from that ordered-tuple space to D, containing the tuple in its source, agreeing with summation on its source, and whose inverse agrees with the chart branch near `c.chart u`. The derivative version must additionally identify the differential after individual normalization.
3. **Actual derivative statement.** One need not use a default ambient `fderivWithin`. An explicit safe option is to extend the local normalized branch arbitrarily outside the chart target, let T be the range of Dφ and L be `inducedDerivative Dφ Dg hinj`, and prove

   `HasFDerivWithinAt normalizedLocalBranch (L.comp (orthogonalProjection T)) chartNeighborhood A`.

   Here `chartNeighborhood` is the inverse image of the chart target in the actual ambient tensor set, and the projection is onto T with the induced norm. The theorem must identify T as the tangent to the chart image. This produces an actual derivative witness along the whole local domain, while avoiding uniqueness/default issues for ambient within-derivatives. An equivalent `HasMFDerivAt` theorem using the induced tangent metric is also acceptable. Existing ratio and slope theorems then identify its intrinsic operator norm exactly.
4. **Canonical probability and expectation theorem.** Define the canonical Gaussian measure from S and its induced volume, and define its angular condition using legitimate local inverses/derivative witnesses. On points where such inverses fail to exist, give it any explicitly documented extended value, for example top. Add a compared theorem with conclusions

   `canonicalInputMeasure = inputMeasure ∧`

   `(∀ᵐ A ∂canonicalInputMeasure, canonicalAngularCondition A = angularSlope r A) ∧`

   `(∫⁻ A, canonicalAngularCondition A ∂canonicalInputMeasure) < ⊤`.

   Include positive finite canonical normalization and the probability assertion, either here or as consequences compared separately. Generalize the chart area formula to `SmoothIdentifiableChart` if the canonical induced-volume definition needs that fact outside decomposition chart neighborhoods; alternatively prove measure equality using the common full-measure regular sublocus.

Other exact implementations are acceptable. The essential requested change is a formal theorem that reaches the original local-inverse derivative and canonical smooth-locus probability law, with no caller-supplied measure equality, null-set claim, or derivative-correspondence premise. A new predicate named "canonical" defined merely as the current angularSlope would not resolve this finding.

## Internal lemmas that need proofs but need not all be additional public targets

Permutation-minimum reduction, chart-independence, normalization derivative rules, finite-dimensional inverse continuity, lower-complex-rank nullity, and nonhomogeneous-polynomial/conic-locus handling may remain internal supporting theorems. Their omission from the public list is not itself a finding, provided the actual proof path establishes them wherever needed. The same distinction applies to proving AE measurability by local derivative norms instead of proving global semialgebraicity of the slope.

## Numerical and trust assessment

The numerical inventory is exact and appropriately avoids decorative computation. Existing symbolic Gaussian integrability covers the radial exponents once the geometric reduction is proved. Nothing in this review permits adding a finite-link-integral premise, a custom finite-volume axiom, or a generic-real-regularity assumption to make the proof smaller. LeanCert kernel mode would govern any numerical certificate later introduced; it cannot replace these mathematical obligations.

Resolve R2-1 and R2-2 in revised actual definitions/signatures and update the numerical inventory to match. Then re-request byte-specific independent statement review before implementing proofs. Canonical TR-06 status should remain Solved until all proof, correspondence, independent final review, reproducibility, Comparator, and axiom gates are complete.
