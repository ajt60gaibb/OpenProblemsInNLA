# TR-06 independent byte-specific draft statement review

Reviewer: `/root/tr06_statement_referee_1`, independent AI agent, 24 September 2026.
Phase: pre-proof statement/fidelity review. Implementer: another agent.
**Verdict: REQUESTED CHANGES.** The five existing signatures appear mathematically sound and the concrete numerical model is nonvacuous, but the declared source correspondence is incomplete. Approval of complete TR-06 statement correspondence is withheld. This is not a mathematical disproof or a Lean verification claim.

## Frozen inputs

Exact inspected files were copied into `/private/tmp/tr06-review1/draft-frozen/` before further edits:

| File | SHA-256 |
|---|---|
| `NLA/TR06/Definitions.lean` | `3e73af048a749d1592677ca4f611fbc6784c506a27724c0cf886a3a52bd49712` |
| `Challenge.lean` | `b5a0d73fb544064c77d9fb102851758177fff3b42a06777a12249ac1d7cdd012` |
| `NUMERICAL_TARGETS.md` | `985a80f78083e40e9f9b440591b848fb9c1786d9de7cc22d004b8a06c184a271` |
| `README.md` | `ec2f48fcd96d35ba256264df08e04b88a0faea6512cfe0b4299f497a681b8021` |

Canonical README SHA-256 `f364f4b2ad51065c17d7dd08ea32e729a5d53a8333f0785a11a368165942de6b`; complete Colbrook manuscript SHA-256 `65f9b731628a7a9ab0580d8522cead94bf7e4599ee3c4285e485287d35d451b2`. These were independently reviewed earlier in this review session. Full source review: `/private/tmp/tr06-review1/prestatement-review.md`.

## Definition-by-definition findings

- `TensorIndex`, `Tensor`, `pureTensor`, `RankOne`, `Decomposes`, `ExactRank`: correct actual tensor-coordinate formulation. Rank one explicitly excludes zero; minimality excludes every smaller length including zero. The real and complex coefficient types are distinct and appropriate.
- `Identifiable`: alone this is vacuous when no decomposition exists, but every public use under review conjoins `ExactRank` or assumes `Decomposes`. No current vacuity results. A comment that this predicate expresses uniqueness alone would prevent future accidental use.
- `GenericComplexIdentifiable`: the witness is a COMPLEX exact-rank-r tensor with nonzero polynomial evaluation, correctly excluding a polynomial vanishing on the entire secant image. There are no analytic consequences hidden in the predicate. The representation is mathematically equivalent to a proper algebraic exceptional-set condition, but that equivalence is only prose at present: see R1.
- `expectedDimension`: correct formula under the format bounds. This is a number, not an assertion that the actual locus has that dimension; the regular-locus existence obligation appropriately remains a theorem.
- `identifiableRealSet`: correct real exact-rank-r and real uniqueness domain. Real tensors of smaller complex rank and exceptional complex-nonidentifiable points must be removed by proved null-set geometry, not assumed absent.
- `AngularOutput`, `normalizedTuple`: correct l2 product Frobenius norm, with each recovered summand individually normalized before taking differences or derivatives. Flattening avoids the default function-space sup norm.
- `angularDistance`: the all-decomposition infimum includes every ordering and therefore represents the permutation minimum on identifiable inputs. The nonempty exact-rank hypothesis excludes empty-infimum artifacts on the sampling set. It is correctly a pseudodistance, zero along positive radial rays.
- `angularSlope`: correct extended pointwise local Lipschitz ratio with a punctured approach set. `B != A` makes the ENNReal denominator positive; all finite-dimensional ambient distances are finite. The infimum over positive radii gives the intended local limsup. The entire identifiable set occurs in the approach domain, so correspondence needs a genuinely relatively open local image, which the chart definition supplies.
- `tensorVolume`, `gaussianWeight`, `unnormalizedInput`, `normalization`, `inputMeasure`: correct explicit volume-Gaussian construction with no supplied measure or normalizer. I independently inspected pinned Mathlib `Geometry/Euclidean/Volume/Measure.lean`: `μHE[k]` is Euclidean-normalized, unlike `μH[k]`. The current draft correctly uses μHE, so my earlier raw-Hausdorff scaling caution does not apply to these bytes. The nonlinear area bridge remains essential.
- `derivativeRatio`, `inducedDerivative`: correct induced-input operator construction under injectivity. The real division gives zero at v=0; injectivity ensures that is the only zero denominator in the correspondence theorem. The supremum therefore correctly includes all directions without a unit-sphere restriction.
- `DecompositionChart`: the target is open in the entire identifiable subtype; it is not merely an immersed subset. C1 ambient input plus injective derivative makes the chart an embedded C1 parametrization. C1 summands and normalized output are valid requirements. The output smoothness field is redundant but benign. However, the comment says smooth while the fields say only C1, and this chart is not yet tied to the canonical C-infinity smooth locus or to the local inverse of ordered addition: see R2 and R3.
- `regularSet`, `regularVolume`, `regularNormalization`, `regularInputMeasure`: these are explicit C1 branch-regular objects. The definitions do not smuggle the target conclusion into a hypothesis. Their equality with the canonical smooth-locus model still needs declared bridge conclusions.

## Existing Challenge signatures

I found no counterexample to the five current statements. `derivativeRatio_eq_operatorNorm` includes the degenerate zero-dimensional case correctly. `angularSlope_eq_chart_derivative` needs the finite-permutation separation argument, but its assumptions suffice. `induced_volume_chart` is a genuine nonlinear area formula for an injective C1 chart and uses the correct rectangular `normDet`, not an ordinary square determinant. `regular_locus` correctly makes measurable/nonempty/full-measure regularity conclusions rather than assumptions. `finite_angular_mean` requires positive finite mass, normalized probability, AE measurability, and ENNReal finite integrals, preventing Bochner-default false positives.

None of these observations approves their unimplemented proofs. In particular no finite-volume theorem, generic regularity theorem, area formula, or polar formula has been proved by elaborating this Challenge.

## R1 — Missing algebraic-exception equivalence signature

**Location:** Definitions lines 54–61; Challenge has no corresponding theorem.

The source hypothesis is specified using a proper algebraic exceptional set. The principal polynomial predicate is a good encoding but its advertised equivalence is not among the required theorem signatures. Add a source-side definition using arbitrary polynomial zero sets and require the equivalence.

A minimal exact source-side definition uses `P : Set (MvPolynomial (TensorIndex d n) ℂ)` and

```text
exception(P) = {A | forall p in P, eval(A,p)=0}.
SourceGenericComplexIdentifiable := exists P,
  (exists A, ExactRank r A and A notin exception(P)) and
  (forall A, ExactRank r A -> A notin exception(P) -> Identifiable r A).
```

Required signature:

```lean
theorem genericComplexIdentifiable_iff_source (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
  GenericComplexIdentifiable d n r ↔ SourceGenericComplexIdentifiable d n r
```

This is an elementary representation bridge: select a polynomial separating the witness from the zero set in one direction; use a singleton polynomial family in the other. If instead the source predicate is defined through a secant Zariski closure, include the rank-r image density/irreducibility facts needed for that precise encoding. Never weaken properness to a set that may contain the whole rank-r locus.

## R2 — Missing canonical smooth domain and direct canonical expectation

**Location:** Definitions lines 133–161; Challenge `regular_locus` and `finite_angular_mean`.

The current regular set is defined using C1 decomposition charts. The canonical domain is the smooth identifiable locus, with its intrinsic derivative and induced volume. The README honestly acknowledges the unresolved relation, but a complete Challenge must require it formally.

Constructively define:

1. `SourceSmoothChart`: an INPUT-ONLY C-infinity `OpenPartialHomeomorph` from the k-dimensional Euclidean coordinate space into the whole identifiable set, whose ambient input derivative is injective. It has no decomposition field. `sourceSmoothSet` is the union of these images. This represents the canonical smooth identifiable input locus independently of regularity of its inverse problem.
2. `SmoothDecompositionChart`: such a source chart plus C-infinity actual ordered summands satisfying `Decomposes`, and C-infinity normalized output (or derive the latter). `smoothRegularSet` is its image union. Each such chart also yields a C1 `DecompositionChart` by forgetting regularity.
3. `sourceVolume := μHE[k].restrict sourceSmoothSet`, `sourceNormalization`, and `sourceInputMeasure` from exactly the same Gaussian weight and their own mass.
4. `sourceAngular A`: ENNReal supremum of the genuine induced operator norms over all smooth decomposition charts and all coordinates mapping to A. At points with no such chart the supremum is zero. This exceptional convention becomes legitimate only after proving those points null.

Required signatures (schematic names, exact mathematical content):

```text
smooth_locus_correspondence(format hypotheses, SourceGenericComplexIdentifiable):
  MeasurableSet sourceSmoothSet and MeasurableSet smoothRegularSet and
  smoothRegularSet subset sourceSmoothSet and
  tensorVolume (identifiableRealSet \ smoothRegularSet)=0 and
  sourceVolume = regularVolume.

source_angular_eq_chart(c: SmoothDecompositionChart,u in c.source):
  sourceAngular(c(u)) = ofReal(norm(the induced derivative of normalize∘summands)).

source_angular_eq_slope_ae(format hypotheses, source generic hypothesis):
  sourceAngular =ae[sourceVolume] angularSlope.

source_inputMeasure_eq(format hypotheses, source generic hypothesis):
  sourceNormalization=normalization and sourceInputMeasure=inputMeasure.

finite_angular_mean_source(format hypotheses, source generic hypothesis):
  0<sourceNormalization and sourceNormalization<infinity and
  IsProbabilityMeasure sourceInputMeasure and
  AEMeasurable sourceAngular sourceVolume and
  integral(sourceAngular,sourceInputMeasure)<infinity.
```

The final theorem's only substantive assumptions remain the original format and complex generic-identifiability conditions. Source canonical norm and measure must be defined by explicit derivative/Jacobian constructions, not by aliases to angularSlope/inputMeasure. The existing induced-volume chart theorem may be generalized to input-only C1 charts, then applied to SourceSmoothChart; this identifies sourceVolume with actual induced volume without relying on the existence of summand branches for its definition.

An alternative simpler presentation may strengthen `DecompositionChart` directly to C-infinity and add the input-only SourceSmoothChart and its null-complement bridge. Either is acceptable if all source correspondences are explicit and reviewed.

## R3 — Missing actual local inverse of ordered addition

**Location:** `DecompositionChart.decomposes` and the local correspondence Challenge.

The current branch field establishes a smooth right inverse on the input image. For source fidelity, explicitly connect it to the canonical local inverse of the addition map on ACTUAL ordered nonzero rank-one tensors, not just a selected right inverse among already-identifiable inputs.

Let

```text
OrderedRankOne := {a : Fin r -> Tensor real d n | forall i, RankOne(a_i)}
```

with its inherited topology, and `addition(a)=sum_i a_i`. For each smooth decomposition chart c and u in its source, require:

```text
smooth_chart_is_local_addition_inverse(c,u):
 exists e : OpenPartialHomeomorph OrderedRankOne sourceSmoothSet,
   base_tuple(c,u) belongs to e.source and
   (forall a in e.source, value(e(a)) = addition(a)) and
   exists W, IsOpen W and u in W and W subset c.source and
     (forall v in W,
       value(e.symm(lift_to_sourceSmoothSet(c(v)))) = c.summands(v)).
```

This states that e.source is open in the WHOLE ordered rank-one product, identifies e with actual summation, and identifies its inverse with the reviewed branch near the base point. The input point lift is justified by c's SourceSmoothChart component. Its inverse derivative is therefore exactly the induced derivative used for sourceAngular.

The expected proof uses smoothness/dimension of the Segre product, injectivity of the input chart derivative, the chain rule, and the inverse function theorem. Merely proving a left inverse among tuples whose sum is already known identifiable would not provide the same open-source claim. This additional proof is substantive but belongs to complete-target correspondence.

## Documentation and numerical inventory

Attribution is correct and includes George Stepaniants and the requested Caltech department without adding a contact email. Colbrook's original proof credit is preserved. README and NUMERICAL_TARGETS correctly say incomplete, no Comparator acceptance, and no final review. There is no finite numerical certificate in the mathematical source; avoiding decorative LeanCert calculations is appropriate. The radial exponents and Gaussian coefficient are correct. No existing canonical statement, number, status, or verification was changed during this review.

## Mechanical evidence and limitations

I ran an independent statement-only typecheck of the frozen files, using the specified Lean 4.33.1 binary and pinned existing package build artifacts, with separate output `/private/tmp/tr06-review1/typecheck-build/`. Log: `/private/tmp/tr06-review1/typecheck.log`. This is a local elaboration check with deliberate Challenge sorry placeholders, NOT reproducible Linux proof verification. No Solution, kernel trust audit, transitive permitted-axiom report, or Comparator result was inspected because none exists for this candidate.

**Disposition:** resolve R1–R3 in actual definitions/signatures and return the new byte hashes for independent re-review. These are correspondence requirements, not requests to alter the original mathematical target. No complete-target statement PASS has been issued.
