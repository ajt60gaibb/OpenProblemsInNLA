# TR-06 independent revised pre-proof statement review

Reviewer: `/root/tr06_statement_referee_1`, independent AI agent, 24 September 2026.
Phase: revised statement, canonical-source fidelity, nonvacuity and numerical inventory review BEFORE proof implementation.

**Verdict: APPROVE the complete ten-declaration pre-proof statement boundary at the exact hashes below.** This approval means that proving every required declaration with the prescribed kernel, correspondence, axiom and Comparator gates would establish the canonical TR-06 target. It does not mean any required theorem has been proved. All ten Challenge proof bodies remain intentional `sorry` placeholders. Canonical status must remain Solved, not Lean verified.

## Exact reviewed inputs and independent elaboration

I read the complete Definitions, Challenge, NUMERICAL_TARGETS and README from the real worktree and independently computed their hashes. Copies are frozen under `/private/tmp/tr06-review1/revised-frozen/`.

| File | SHA-256 |
|---|---|
| `NLA/TR06/Definitions.lean` | `e5fe5314f4c17df41b5bec54f2c407b2d1eba8ba59be5d85525de13e262f8898` |
| `Challenge.lean` | `5706c286e2d184965962c31c01805a4d119696459e5bc6e2f90226587e452fbe` |
| `NUMERICAL_TARGETS.md` | `e3a0b1fd548018a1b7afe60d857ff88cf672a429039d240f63068ae4502e355a` |
| `README.md` | `85f8b768d76749fe1b0c25f0de070efc3dd832a459fb66aad16d014e41d2fb5c` |

Canonical TR-06 README SHA-256 `f364f4b2ad51065c17d7dd08ea32e729a5d53a8333f0785a11a368165942de6b`; complete Colbrook manuscript SHA-256 `65f9b731628a7a9ab0580d8522cead94bf7e4599ee3c4285e485287d35d451b2`. My earlier independent source review remains `/private/tmp/tr06-review1/prestatement-review.md`.

I independently ran the frozen revised files through the specified Lean 4.33.1 binary using the pinned existing Mathlib/package artifacts and a separate output directory `/private/tmp/tr06-review1/revised-typecheck-build/`. Definitions and Challenge each exited zero. Challenge emitted precisely ten `declaration uses sorry` warnings, one for each declared obligation. Log: `/private/tmp/tr06-review1/revised-typecheck.log`. This checks elaboration, not mathematics, proof independence, reproducible Linux execution, or permitted axioms.

## Resolution of the prior requested changes

The prior report `/private/tmp/tr06-review1/draft-statement-review.md` remains REQUESTED CHANGES for its old hashes. The following closes its findings specifically for the revised bytes; no old approval is invented.

### R1 — Source genericity equivalence: CLOSED

`SourceGenericComplexIdentifiable` explicitly describes an algebraic exceptional set by an arbitrary family of complex coordinate polynomials. Its witness is an exact-rank-r complex tensor outside their common zero set. The required `generic_iff_source` theorem relates that source predicate to the principal-polynomial predicate.

This is a faithful relative-properness encoding. An arbitrary polynomial merely nonzero as a syntactic polynomial could vanish on the whole secant image; the witness here prevents that. An arbitrary family is not a stronger analytic assumption: choosing one member nonzero at the witness gives the principal formulation, and a singleton family gives the reverse implication. Neither definition contains integrability, a probability measure, regularity, finite volume, or the desired conclusion.

### R2 — Canonical smooth domain and expectation: CLOSED

`SourceSmoothChart` now gives C-infinity embedded input charts into the entire real identifiable exact-rank-r set, with injective ambient differential. It contains no summand branch. The type `((top : ENat) : WithTop ENat)` correctly selects C-infinity regularity in the pinned ContDiff API. Its union `sourceSmoothSet` therefore represents the canonical smooth identifiable input locus in explicit Euclidean coordinates, rather than defining that locus to mean the desired inverse problem is already regular.

`SmoothDecompositionChart` adds C-infinity actual summands and normalized output. `sourceAngular` is built from the genuine induced tangent operators at these presentations, not from angularSlope or its finite integral. The input differential is inverted onto its range with the inherited Frobenius norm, and the output uses the flattened l2 product Frobenius norm. Thus its constituent operators are exactly the chart representations of the canonical normalized-summand derivative once R3's declared inverse bridge is proved.

The supremum in sourceAngular avoids global labeling. The existing universal chart/slope and derivative-ratio/operator-norm obligations imply equal norms for any two smooth presentations at a point: forget each smooth chart to a C1 DecompositionChart, apply both universal equalities, and obtain the same angularSlope. Therefore the supremum equals each legitimate local derivative norm wherever a smooth decomposition chart exists. No extra assumption of global labeling or coordinate invariance is hidden here.

`smooth_locus_correspondence` requires measurability, inclusion of the smooth decomposition locus in the smooth input locus, full tensor volume of the former, and equality of the source and C1 regular measures. Consequently the empty-chart supremum convention can affect only a proved null set. `source_model_correspondence` explicitly requires equality of the actual normalization constants and probability laws and AE equality of sourceAngular with angularSlope. `finite_angular_mean_source` then states positive finite normalization, a probability law, AE measurability and finite ENNReal expectation under precisely the source assumptions.

The sourceVolume is Euclidean-normalized Hausdorff measure. The existing nonlinear `induced_volume_chart` obligation proves its chart Jacobian formula on each decomposition chart. Together with the full-measure smooth decomposition locus and measure equality obligations, this identifies the source measure with induced Euclidean volume up to the allowed null set. An additional area theorem for input-only charts would be reusable, but is not logically necessary for complete correspondence once the required full-measure chart and measure-equality statements are proved.

### R3 — Actual open local inverse of addition: CLOSED

`OrderedRankOne` is the actual ordered product of nonzero rank-one tensor summands with its inherited topology; it is not pre-restricted to identifiable tuples. `IsLocalAdditionInverse` requires an `OpenPartialHomeomorph` from that whole space to the source smooth locus whose forward map equals the actual sum on its open source. Its coordinate neighborhood clause places the given summands in the partial homeomorphism's source and identifies their image with the input chart.

This clause is equivalent to the required local inverse identification: for every v in the neighborhood, the witnessed tuple a has exactly the prescribed coordinates, lies in e.source, and maps to c(v); applying the built-in inverse law gives e.symm(c(v))=a. The base coordinate belongs to the neighborhood, so the base tuple is included. Both domain and target neighborhoods are open in the correct actual spaces. `smooth_chart_is_local_addition_inverse` requires this property for every smooth decomposition chart at every source point under the admitted format bounds.

The result may require substantial Segre geometry and an inverse-function argument to prove. That difficulty has not been removed by weakening the signature or assuming the local inverse as a field.

## Complete-target checks

- All orders d>=3, all mode sizes n_j>=2, and all ranks r>=3 under genuine COMPLEX generic identifiability are quantified. No admissible perfect format, large rank, sign, or endpoint is silently excluded.
- The sampling tensors, rank, decompositions and smooth manifolds are REAL. The generic assumption is COMPLEX. Any real-rank/complex-rank exceptional discrepancy must be handled in the regular-locus proofs.
- Rank-one objects are actual nonzero tensors, so factor-rescaling ambiguity is correctly removed. ExactRank excludes every smaller decomposition; uniqueness is only modulo permutations.
- Normalization is componentwise and occurs BEFORE every derivative. The input and output norms are exactly Frobenius and l2 product Frobenius, not the default sup norm on a function space.
- The local slope uses the full actual identifiable set, with punctured neighborhoods and an extended nonnegative quotient. The source quantity independently uses genuine tangent operators. Required correspondence makes their relation a theorem rather than an alias.
- The Gaussian coefficient is exactly 1/2. The density is measured against induced input volume, not a distribution of summands or factors. Both normalizers are defined from their own actual measures and must be shown positive and finite.
- `μHE`, not raw `μH`, is used. Its Euclidean normalization is verified in the pinned Mathlib source; the required nonlinear area formula uses the rectangular Gram-volume factor `normDet`.
- Genuine lintegral finiteness and AE measurability prevent zero-valued Bochner-default artifacts. The final theorem has no caller-supplied measure, integral bound, regular cone, finite-volume certificate, or theorem-valued hypothesis encoding the conclusion.
- The polynomial witness need not be homogeneous. The documentation correctly warns that a particular polynomial nonvanishing set is not automatically a cone. Conical/full-measure reduction must be derived, not silently assumed.
- The source asks only a finite first expectation. The Challenge does not substitute an ordinary condition number, a scalar quotient of that condition number, a higher moment, or a uniform bound across formats.

## Numerical and proof-plan review

The mathematical source is qualitative. Its scalar radial requirements use k=r(1+sum(n_j-1)), numerator exponent k-2, denominator exponent k-1, positive radius, and Gaussian exp(-t^2/2). The admitted dimensions give k>1, which controls the origin. No exact Gamma value or interval subdivision is needed. The inventory appropriately avoids a decorative LeanCert calculation.

The central missing proof is bounded semialgebraic normalized-graph integrability, together with real regularity, graph area and polar disintegration. These remain genuine kernel proof obligations. Nothing in this statement approval certifies that the pinned libraries already provide them. Every required declaration, including the source correspondence declarations, must be compared against the approved Challenge; proving only finite_angular_mean would not satisfy this boundary.

## Attribution, preservation and limitations

George Stepaniants and the Department of Computing and Mathematical Sciences, California Institute of Technology are credited without a contact email. Matthew J. Colbrook's original mathematical proof attribution is preserved. The original problem authors and probability model are identified. The docs explicitly disclose AI-assisted preparation and incomplete proof status. No canonical README, original statement, permanent ID/path, status, or prior verification was changed by this reviewer.

This reviewer inspected no Solution proofs, reproducible Linux proof-verification result, TR-06 Comparator result, LeanCert certificate, or transitive permitted-axiom report; none is established by the reviewed preparation. Independent final proof, fidelity and API/attribution reviews remain required after implementation. A changed definition or required theorem signature invalidates this byte-specific approval until reviewed again.

**Final disposition: APPROVE for pre-proof statement implementation only, with R1–R3 closed at these exact revised hashes. No formal verification or publication-as-verified approval is given.**
