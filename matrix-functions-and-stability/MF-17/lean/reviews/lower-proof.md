# MF-17 statement fidelity, lower bound, endpoint, and attribution review

Date: **2026-09-30 (UTC)**. Phase: **retrospective statement-fidelity and proof-source review** of an imported formalization. Reviewer: **Aquinas, independent AI reviewer (task 01a0f233-bfc7-7e03-a460-93aeb5dd43d2)**. I am a nonimplementing reviewer and made no proof or packaging changes. This is not human peer review, not a review predating implementation, and not an official Tau Ceti review.

**Current verdict: approve after documentation corrections**, within the checked scope and limitations of this source-level review. See the [final incorporation verdict](#final-incorporation-verdict--2026-09-30), which resolves both documentation objections. All five Challenge signatures retain source-level statement-fidelity approval; mechanical verification remains separate. The original findings and requested corrections are retained below as review history.

**Mechanical status:** I did not execute Lean, Lake, an axiom audit, or Comparator, and inspected no build, axiom, or Comparator logs. The parent handles those gates. Source inspection and the lexical/import checks reported here do not establish kernel acceptance or justify the label “Lean verified.”

## Independent statement-fidelity comparison of all five contracts

This is my own comparison, made directly from `Challenge.lean`, all of `Definitions.lean`, the five solution-side declarations, the canonical README's **Original problem statement**, the corresponding portion of `problem.tex`, `NUMERICAL_TARGETS.md`, and manuscript Theorem S.1.1. I did not read or rely on another statement review. This covers the statement-fidelity responsibility as well as the lower-proof responsibility, retrospectively. It is not a claim that the required two independent reviewers or the mechanical gates have all completed.

**Common definition boundary.** The original target ranges over complete complex Hilbert spaces and generators of strongly continuous semigroups, not just matrices, bounded generators, real spaces, or separable spaces. `Definitions.lean:19` represents the semigroup on all real inputs but imposes identity, composition, strong continuity, and the bound only on the nonnegative half-line. Negative values are unused; this allows an arbitrary extension of an ordinary nonnegative-time semigroup and imposes no extra negative-time dynamics. `strong_continuous` is continuity of each orbit, not operator-norm continuity. `InnerProductSpace ℂ H` together with `CompleteSpace H` specifies a complete complex Hilbert space; no `Nontrivial`, separability, or dimension assumption is imposed on the general class.

At `Definitions.lean:30`, the full right derivative at zero is the usual infinitesimal-generator graph. Its domain is all vectors for which that derivative exists. There is no freely chosen graph, restricted domain, everywhere-defined-generator hypothesis, or resolvent estimate built into it. Density/closedness of the generator are standard consequences of the C₀-semigroup hypotheses, not extra assumptions restricting this class; this statement inspection does not purport to reprove the whole generator theory. The sign agrees with `T(s)=exp(sA)` and `exp(tA⁻¹)`, rather than the alternative convention with generator `-A`.

At `Definitions.lean:34`, `IsGeneratorInverse T B` requires `GeneratorGraph T x y ↔ B y=x` for all `x,y`. The reverse implication at `x=B y` provides a preimage of every `y` in the actual generator domain; the forward implication supplies the other inverse identity. `B : H →L[ℂ] H` is an everywhere-defined bounded complex-linear operator. Thus the definition neither presupposes the main growth estimate nor merely asserts an inverse on a chosen subspace. `inverseEvolution` is the operator exponential, not a scalar or spectral surrogate.

`attainableNorms` at line 48 existentially packages all these spaces, semigroups, and inverses, with ordinary continuous-linear-map operator norm. `growthEnvelope` is the real supremum of that set. A real supremum alone does not certify boundedness or nonemptiness: those are separate substantive obligations, supplied by the boundedness contract and the actual scalar examples. Existence/uniqueness of the generator inverse prevents the packaging from silently discarding members of the original class or introducing alternative inverses. The universe `u` is arbitrary and fixed throughout each theorem; the statement does not promise one common set or one simultaneous quantified choice of constants across all Lean universes.

| Challenge declaration | Definition expansion and original-target comparison | Source-level verdict |
| --- | --- | --- |
| `stableSemigroup_hasGeneratorInverse`, lines 10–12 | For every real `M≥1`, every complete complex Hilbert space in `Type u`, and every `StableSemigroup M H`, concludes `∃! B, IsGeneratorInverse T B`. There is no assumed inverse. This formalizes the original statement's consequence of exponential stability that `0` is in the resolvent and the inverse is bounded, including the additional endpoint `M=1`. Uniqueness is appropriate for the full generator, and the zero space is not excluded. | Approve. It is a supporting resolvent contract, not a replacement for the asymptotic question. |
| `attainableNorms_bddAbove`, lines 15–16 | For every `M≥1` and every real `t≥0`, bounds the entire set of inverse-exponential norms over the class. The bound may depend on `M,t` but is uniform over spaces and generators. It is a genuine finiteness obligation, not the tautology that a real-valued definition returns a real number. It supplies the valid real-supremum interpretation needed by the original `G_M`. | Approve. It includes time zero and `M=1`; it does not alone assert nonemptiness. |
| `sharp_growth`, lines 19–23 | For each `M>1`, chooses positive real `c,C,t₀` before every real `t≥t₀`, and bounds the same `growthEnvelope M t` below and above by positive multiples of `growthLog(t)^growthExponent(M)`. The expansion is exactly `L(t)=log log(t+e^e)` and `α(M)=(2/π) arccos(1/M)`. Neither constant depends on a particular space, generator, or observation time. Both inequalities are non-strict, and coverage is the whole half-line, not a subsequence or an asymptotic limsup. | Approve. This supplies the particular sharp rate claimed in S.1.1 as an answer to the original request to determine an order. |
| `finite_dimensional_lower`, lines 26–29 | For each `M>1`, chooses positive `c,t₀` before `t`, then expands `HasFiniteWitness` into a complete finite-dimensional complex Hilbert space, a semigroup with the exact same prescribed upper bound `M exp(-s)`, and a full generator inverse whose actual operator exponential has norm at least `c L(t)^α(M)`. The dimension and every witness object may depend on `t`. No uniform dimension or one universal witness is asserted. | Approve. This is the finite-dimensional strengthening explicitly claimed in S.1.1, consistent with the original unrestricted envelope. |
| `contractive_envelope`, lines 32–33 | For every real `t≥0`, fixes `M=1` and concludes the equality `growthEnvelope 1 t=1`. It includes `t=0`; it is a supremum statement, not equality of every member's norm or a claim of attainment. | Approve. This is the separate endpoint extension in S.1.1/S.9; the original `M>1` asymptotic alone would not imply it. |

The supporting inverse and boundedness contracts are mathematically necessary infrastructure for the supremum formulation, not substituted goals. Finite-dimensional sharpness and the contractive equality are explicit additional claims from the submitted theorem. None of these extras narrows the upper-bound class in `sharp_growth`.

Two apparent wording differences do not weaken the target. First, S.1.1 displays `0<c_M≤C_M<∞`, whereas Challenge separately states positivity of finite real `c,C`. Its two inequalities at `t=t₀`, where `L(t₀)>0`, imply `c≤C`. Second, requiring a positive threshold is harmless for an eventual assertion with a finite threshold: it can always be enlarged. For `M>1`, `0<α(M)<1`; and for `t≥0`, `L(t)≥1`, so neither real powers nor a zero lower multiplier hide a vacuous conclusion. The positive finite-dimensional lower bound also rules out using the zero space as its eventual witness, while permitting the zero space in the general envelope remains correct.

I independently compared each solution-side signature with Challenge: `Solution.lean:19`, `Envelope.lean:43`, `SharpGrowth.lean:25`, `LowerBound.lean:14`, and `Endpoint.lean:20`. A Python source-text extraction also found all five identical after whitespace normalization and the harmless proof-binder spelling change `_hM` to `hM`. This is a source check only: it does not inspect elaborated theorem types, synthesized instances, universe instantiations, or replace the required Lean/Comparator run. The deliberate Challenge placeholders are not evidence of proof.

No claim of a normalized limiting constant, optimal leading coefficient, constants uniform as `M↓1`, or manuscript Part IX follows from these signatures, and none is needed for the original asymptotic-order target. I found no statement-fidelity correction to request for the frozen Challenge/Definitions bytes.

## Required documentation corrections

1. **Distinguish the implemented scalar lower construction from the cited manuscript construction.** `ProofProject/SourceWeightFactor.lean:8` calls its definition the source's “exact principal-power formula”; the definition at line 27 is

   ```text
   ψ(z) = ((1+z)/(1-z))^(α/2)
          exp((α/4)((1-z)^ν - (1+z)^ν)),  ν=(1-α)/2.
   ```

   Part VI, (S.7.2), printed p. 50 / PDF p. 51, instead defines

   ```text
   h(z) = (1-z)^(-α/2) exp((α/4)((1-z)^ν - 1)).
   ```

   It then uses the two-component matrix factor in (S.7.6), printed p. 51, and component sign interchange in Proposition S.7.2(iv). The Lean route uses scalar weighted monomials (`SourcePolynomialHilbert.sourceUnitFamily`), alternating coefficients (`SourcePolynomialGain.sourceUnitFamily_alternating_gain`), replication, and a separate Euclidean metric perturbation (`MetricMargin`, `RoundedSpace`). It does not literally implement that displayed two-component model or its finite-degree strict deficit. In particular, the formal construction has `N=r*n`, metric margin of inverse-square order, and separation parameter `n^3`; (S.8.1) uses `N=2*r*n` and a margin of order `n^(-(2α+ν))`.

   These are legitimate potential proof replacements under `NUMERICAL_TARGETS.md`, and the inspected replacement estimates are proved in source. The objection is the unqualified identification with the manuscript. Add a short explicit correspondence note identifying the scalar symmetrized variant, the alternating-sign witness, and the later metric perturbation as adaptations. The scalar factor is naturally related to the ratio `h(z)/h(-z)` inside the disk, with principal-power branch justification; that relationship is an explanation to supply, not a literal quotation of (S.7.2). Update or explicitly qualify the “exact source” descriptions, including `SourceDirichletGain.lean:10` and the broad opening of `lean/README.md:3`. If another source actually contains the displayed scalar formula, identify that source and its version instead. No human author should be inferred from the repository owner or a commit account.

2. **Qualify claims that improved constants are exactly those in Part VI.** `CoefficientSquare.lean:126`, documenting `coefficientDeficit_interior_lower`, says its constant is “exactly the one in the source,” but uses `(M^4+1)/(M^2-1)`. Manuscript (S.6.6), printed p. 49 / PDF p. 50, displays `2K^4/(K^2-1)`. Likewise the Lean endpoint surplus in `EndpointDeficit.HasBoundaryEstimate.replicationDeficits` is `1/(4B)`, whereas (S.6.4) uses `1/(8B)`. The Lean two-term square estimate and stationary-equation argument explain the stronger constants; I found no need to weaken them. Describe them as proved refinements, or cite the actual alternative source. A correspondence note can clarify inherited comments while retaining the imported source bytes.

Neither objection requires changing the target statement. Neither is a claim that the formalization plagiarized a human author. Both require truthful descriptions of what was imported and how its proof differs from the cited mathematical source.

## Lower-bound findings

**Statement and quantifiers.** `Definitions.lean:19` uses a genuine strongly continuous semigroup with `‖T(s)‖ ≤ M exp(-s)` for every `s≥0`. `GeneratorGraph` is the full strong right derivative on `Ici 0`, and `IsGeneratorInverse` is the equivalence `GeneratorGraph T x y ↔ B y=x` for every `x,y`. `HasFiniteWitness` at line 58 asks for an actual complete finite-dimensional complex Hilbert space and the norm of `NormedSpace.exp ((t:ℂ) • B)`. It does not encode the desired estimate as an arbitrary axiom or redefine the norm.

`LowerBound.finite_dimensional_lower` quantifies `∃ c t₀, 0<c ∧ 0<t₀ ∧ ∀ t≥t₀, ...`. For a fixed arbitrary universe and fixed `M>1`, the space, semigroup, inverse, and finite dimension are chosen inside the time-dependent witness. There is no fixed-dimension requirement, and allowing the dimension to grow is necessary to the construction. The conclusion uses the same `M`, not a nearby larger parameter. `growthExponent` is exactly `(2/π) arccos(1/M)`, and `growthLog` is `log(log(t+exp(exp 1)))` with natural logarithms. `GrowthRate` proves positivity and strict monotonicity on the nonnegative time axis. No uniformity as `M↓1` is claimed.

**The apparent main-estimate premise is discharged.** `SourceBoundaryLower.finite_dimensional_lower_of_source_boundary` is explicitly conditional, but `LowerBound.lean:18` supplies `sourceBoundaryConstant M`, its positivity, and `sourceUnitFamily_hasBoundaryEstimate` for every dimension. `SourceBoundaryEstimate` constructs that estimate from concrete analytic functions, orthogonality, phase energy, and weighted Cauchy–Schwarz. Thus the public theorem does not merely rename a conditional main estimate. The conditional `HasBoundaryModel`, `HasReplicationDeficits`, and `HasFiniteSignModel` interfaces are ordinary intermediate reductions, instantiated along this path.

**Source weight and normalization.** The concrete weight is the scalar formula displayed above. Its principal-power branches are controlled inside the disk; boundary continuity and phase identities omit only `0,±π` as null angles. With `α=growthExponent M`, `SourceWeightParameters` proves `cos(πα/2)=1/M`, `0<α<1`, `ν=(1-α)/2>0`, and `α+ν<1`. The correction gives a positive phase margin bounded below by a multiple of `min(|θ|,π-|θ|)^ν`. `SourceMarginIntegrability` and `PhaseQuotientIntegral` consequently prove actual integrability of `(1+|ψ|²)/δ`; it is not silently assigned the default zero integral of a nonintegrable function.

`SourceBoundaryMoments` obtains the moments of `ψ` and `ψ²` from holomorphic radial means and dominated convergence with an integrable common majorant. `FiniteMomentOrthogonality` and `FiniteMomentCoefficients` then prove the disjoint-support orthogonality and adjacent coefficient extraction used in `SourceBoundaryEstimate`. The extraction has factor `2π`, while the squared Hilbert norm is divided by the positive raw mass `D=∫|ψ|²`. `source_phase_deficit_div_mass` explicitly converts the raw phase deficit to the normalized Hilbert deficit. The boundary constant `1+J(6D+D⁻¹)` is positive and depends on `M` before the dimension. The different normalization of angular measure does not lose a power or a parameter.

Mathlib conjugates the first inner-product argument, unlike the manuscript's stated convention. `SourcePolynomialInner`, `PhaseIntegralEnergy`, and `CoefficientSquare` handle that convention explicitly. The cross integral is the conjugate of the proved analytic-square moment, and coefficient extraction leaves the coefficient itself unconjugated.

**Exact exponent and a genuine gain vector.** `SourceDirichletGain` bounds the numerator energy below by a positive multiple of `n^(1+α)` and the reflected-weight denominator above by a positive multiple of `n^(1-α)`. Half-turn translation identifies the latter with the alternating coefficient polynomial. `source_dirichlet_reflected_gain` takes `d=sqrt(A/C)>0`; the squared gain is `(d*n^α)^2`, so the norm exponent is `α`, not `α/2` or `2α`. `SourcePolynomialGain` transfers it to the actual normalized Hilbert family. The alternating vector is nonzero for `n≥1`. No norm-attainment assumption is used. Adjacent-tail bounds control coefficient energy, preventing a spurious gain obtained solely from a zero synthesized input.

**Uniform replication.** `EndpointDeficit` derives surplus `1/(4B)` and interior deficit coefficient `(M^4+1)/(M^2-1)`. `BoundaryLower.lean:37` chooses a replication count satisfying the required budget before introducing `n`. `ReplicationEnergy`, `ReplicatedSpace`, and `ReplicationModels` realize group means and zero-mean deviations in an actual Hilbert product. The constant-copy coefficient lift preserves synthesis norms, and the copied sign multiplier turns the repeated alternating vector into the repeated all-ones vector. The elementary-pattern bound remains exactly `M`. This is not a dimension-dependent choice of `M` or a replication count chosen after time.

**Rounding, separation, and the actual stable generator.** `MetricMargin` adds the coefficient energy with

```text
η = 1/(4M²N),    γ = (M²-1)/(4M²N²+1).
```

The rounded norm is realized on the range of an injective map into a Hilbert product, not by replacing a norm instance on the original space. Its range is finite-dimensional and complete even when the original source family lives in infinite-dimensional angular L². The energy distortion is at most two, so the sign gain loses only `sqrt(2)`. Pattern norms are at most `sqrt(M²-γ)`. Coordinate norms are rederived in this new metric with bound `2M`.

`ScalarSeparation` covers every nonnegative semigroup time, including the initial interval and the last transition; its total diagonal coefficient error is at most `3ε`. `RoundedSemigroupBound` converts this to `6Mε` and takes `ε=γ/(12M²)`. The explicit inequality

```text
sqrt(M²-γ) + 6Mε ≤ M
```

absorbs the error without relaxing the prescribed class. `SeparationScale` proves the smallness condition eventually for fixed replication count and `κ=n³`. `SeparatedIntegers` constructs positive frequencies with prescribed parity and quadratic separation. These are proved scalar estimates, not a premise that a suitable semigroup already exists.

`DiagonalWitness` uses eigenvalues `ω⁻¹(-1+iy)⁻¹-1`, giving the exact decay factor `exp(-s)`. `BoundedGenerator` identifies the full derivative graph of the operator exponential and checks both inverse identities. The positive choice `ω=(2πMN(1+Y²))⁻¹` gives peak time `2π²MN(1+Y²)` and norm lower bound `exp(-π)*g/sqrt(2)-1`. The additive loss is independent of dimension and time.

**All sufficiently large times.** `PeakClock.peakTime_clock_linear` proves `growthLog(s_n) ≤ C(M,r)*n`. `DiscreteLower.finiteWitness_lower_of_discrete` chooses a positive threshold and `n=floor(growthLog(t)/C)`; the floor retains at least half the clock and the threshold absorbs the additive loss. It obtains `s_n≤t` without assuming monotonicity of the selected peak sequence. `Rescaling.HasFiniteWitness.mono_time` accelerates the original semigroup by `t/s_n≥1`; the generator graph and inverse are scaled reciprocally, and the exponential at the new time equals the old exponential. Thus every real `t≥t₀`, including equality, is covered.

**Envelope and universe bridge.** `HasFiniteWitness.le_growthEnvelope` invokes `attainableNorms_bddAbove` before `le_csSup`. `Envelope` uses the coarse exponential bound, rather than circular reliance on the sharp lower conclusion; its imported inverse norm estimate remains part of the separate generator audit. `SourceBoundaryLower` lifts the concrete angular family to `ULift.{u}` before applying the universe-polymorphic construction. `HilbertULift` retains the existing norm and proves preservation of inner products, synthesis norms, and the boundary estimate. Subsequent products and finite-dimensional ranges stay in the chosen universe. This is universality in an arbitrary fixed universe, not a single set containing all universes.

## Contractive endpoint findings

`Contractive.generatorGraph_re_inner_nonpos` differentiates the nonincreasing squared orbit norm at the right endpoint. `generatorInverse_re_inner_nonpos` uses the full inverse graph at `(Bx,x)`, and `inverseEvolution_norm_le_one_of_dissipative` differentiates the bounded exponential orbit. None of these bounds assumes a nontrivial space or positive time. Consequently the zero Hilbert space is included in the upper estimate.

`ScalarExamples` supplies one-dimensional examples on `EuclideanSpace ℂ (ULift.{u} Unit)` for every `a≥1`, with actual inverse-exponential norm `exp(-t/a)`. These values tend to one as `a→∞`. `Endpoint.contractive_envelope` proves boundedness and nonemptiness before passing to the supremum. It does not claim the supremum must be attained at positive time.

For `t=0`, `Endpoint.attainableNorms_zero_bddAbove` and `growthEnvelope_zero` use `norm_id_le`, valid also on the zero space, rather than incorrectly claiming every identity has norm one. The nontrivial scalar examples supply the value one. Both `G₁(t)=1` for all `t≥0` and `G_M(0)=1` for `M≥1` are supported by the inspected source.

## Trust, reuse, and provenance boundary

A recursive textual import check found 221 local modules in the `Solution` closure: `Solution.lean` and all 220 `ProofProject/*.lean` files, with no missing local import and no reference to `Challenge`. A lexical scan of those files found no `sorry`, `admit`, `axiom`, `sorryAx`, `unsafe`, `implemented_by`, `native_decide`, or `extern`, and no project-local `opaque`, `syntax`, `macro`, `elab`, `initialize`, `run_cmd`, `run_elab`, or `#eval` command. The eight `set_option` occurrences concern heartbeats or elaborator transparency, not a disabled kernel. This is a useful source check, not a substitute for transitive elaborated axiom inspection. `Challenge.lean` deliberately contains five statement-side `sorry` proofs; they are outside the solution import closure.

The toolchain requests Lean 4.33.1. The manifest pins Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`; the sibling supplied project's Mathlib checkout reports that same HEAD. I searched the pinned inner-product sources for a ready-made ULift instance and the normed sources for the isometry API. `HilbertULift.uliftHilbert` reuses `LinearIsometryEquiv.ulift`; no duplicate inner-product ULift instance was found by that targeted search. I also inspected the L² inner-product/norm identities used by the concrete realization. This is not a comprehensive API/naming or Mathlib reuse review.

All 220 copied proof modules were byte-identical to `/Users/april/Documents/overleaf/MF-17/lean/ProofProject/` when checked and rechecked. The copied `LICENSE` is the same complete Apache-2.0 text as the sibling supplied project's license. That sibling project has no top-level NOTICE file. This establishes retention relative to the available supplied copy, not a complete audit of historical third-party notices or a determination of copyright ownership.

The updated canonical problem page calls the result a solution claim, links the local formalization and evidence instructions, says the verification gates remain pending, and does not assert human peer review. `NUMERICAL_TARGETS.md` truthfully discloses importing an existing formalization and retrospective review. The local source README describes an autonomous/model-produced solution; that text does not authenticate any person's authorship. I assign no human mathematical or formalization credit on that basis. No remote was contacted or changed. The report's byte identifiers below bind this review to local evidence; they do not establish a remote release's provenance.

## Actual scope and limitations

I read `NUMERICAL_TARGETS.md`, the repository-root `docs/lean/REVIEW.md`, the canonical problem README and its original-statement TeX rendering, the project README, license, target declarations, and relevant packaging metadata. I extracted manuscript text locally and directly compared Theorem S.1.1 and Sections S.6–S.9 (printed pp. 42 and 49–55 / PDF pp. 43 and 50–56). A wider text extraction/search was used only for orientation and to look for an alternative weight formula. It is not a review of the full manuscript or all its appendices.

The following modules received focused reading of their relevant statements and proof bodies. This records the inspected source path, not a claim that every tactic was independently replayed:

```text
ProofProject/BasisEnergy.lean
ProofProject/BoundaryLower.lean
ProofProject/BoundedGenerator.lean
ProofProject/CoefficientSquare.lean
ProofProject/Contractive.lean
ProofProject/Definitions.lean
ProofProject/DiagonalPeak.lean
ProofProject/DiagonalWitness.lean
ProofProject/DiscreteLower.lean
ProofProject/Endpoint.lean
ProofProject/EndpointDeficit.lean
ProofProject/Envelope.lean
ProofProject/FiniteModelLower.lean
ProofProject/FiniteModelMargin.lean
ProofProject/FiniteModelWitness.lean
ProofProject/FiniteMomentCoefficients.lean
ProofProject/FiniteMomentOrthogonality.lean
ProofProject/GrowthRate.lean
ProofProject/Helpers.lean
ProofProject/HilbertULift.lean
ProofProject/HolomorphicCircleMoments.lean
ProofProject/LowerBound.lean
ProofProject/MetricMargin.lean
ProofProject/PeakClock.lean
ProofProject/PhaseIntegralEnergy.lean
ProofProject/PhaseQuotientIntegral.lean
ProofProject/ReplicatedSpace.lean
ProofProject/ReplicationBound.lean
ProofProject/ReplicationDeficit.lean
ProofProject/ReplicationEnergy.lean
ProofProject/ReplicationLower.lean
ProofProject/ReplicationModels.lean
ProofProject/Rescaling.lean
ProofProject/RoundedOperators.lean
ProofProject/RoundedSemigroupBound.lean
ProofProject/ScalarEigenvalues.lean
ProofProject/ScalarExamples.lean
ProofProject/ScalarSeparation.lean
ProofProject/SeparatedIntegers.lean
ProofProject/SeparationScale.lean
ProofProject/SharpGrowth.lean
ProofProject/SourceBoundaryEstimate.lean
ProofProject/SourceBoundaryLower.lean
ProofProject/SourceBoundaryMoments.lean
ProofProject/SourceDirichletGain.lean
ProofProject/SourceMarginIntegrability.lean
ProofProject/SourceMomentConvergence.lean
ProofProject/SourceMomentDefs.lean
ProofProject/SourcePhaseCorrection.lean
ProofProject/SourcePhaseDefs.lean
ProofProject/SourcePhaseMargin.lean
ProofProject/SourcePhaseMeasure.lean
ProofProject/SourcePolynomialGain.lean
ProofProject/SourcePolynomialHilbert.lean
ProofProject/SourcePolynomialInner.lean
ProofProject/SourceRadialBounds.lean
ProofProject/SourceRadialIntegrability.lean
ProofProject/SourceRadialLimits.lean
ProofProject/SourceWeightBounds.lean
ProofProject/SourceWeightFactor.lean
ProofProject/SourceWeightParameters.lean
ProofProject/TailBoundaryAlgebra.lean
ProofProject/WeightedBoundaryEstimate.lean
ProofProject/WeightedCauchySchwarz.lean
ProofProject/WeightedDirichletBounds.lean
```

`RoundedSpace.lean` received focused inspection of the realization, instances, and norm-comparison portions; `SourcePhasePolar.lean` of the phase/exponential and reflection proofs (lines 141 onward), with earlier declaration inspection. `DirichletKernel.lean` and `AngularPowerIntegrals.lean` were inspected at declaration level only. `Solution.lean` and all five `Challenge.lean` signatures were read. The remaining local closure received import/trust-token scanning and byte comparison, not a full mathematical proof review.

In particular, this report does not independently approve the upper-bound oscillatory/localization argument, the entire unbounded-generator/Laplace theory, every elementary analytic dependency, external Mathlib proofs, compiler binaries, or cached artifacts. `SharpGrowth` was inspected for the final assembly and quantifiers, not as independent certification of its upper half. No prior reports were used as mathematical evidence. Builds, transitive axiom lists, and statement comparison must be tied to the final source separately. Resolving the documentation findings would remove this review's concrete objections; it would not by itself complete those mechanical gates or the other independent review responsibilities.

## Checked byte identifiers

SHA-256, captured for the reviewed working-tree files. The canonical README was reread after its local-source/evidence-link update; its current digest is in the table. Its earlier inspected prose had digest `f6c51ef1deef07bbd10d6d72251ed8467bbd17b235a5adfc9e04875241ce9daf`. That prose update did not change the original mathematical target. The frozen proof-tree and Challenge digests were rechecked unchanged during the statement-fidelity addition. Paths below are relative to this Lean project. Aggregate digests use UTF-8 records `relative-path + NUL + lowercase-file-sha256 + LF`, sorted lexicographically by relative path, followed by SHA-256 of the concatenated records.

- Entire scanned local solution source: **221 files**, `Solution.lean` plus all 220 `ProofProject/*.lean`; aggregate `e207a749abbd7ca013ebd3faf4071b0563fd547618c08672a15b918f9ea56170`.
- Focused/partial scope enumerated above plus `Solution.lean` and `Challenge.lean`: **71 files**; aggregate `42de0cc9f457f174e64f1529e2d29a4620f3592ebefd50dedc63a0be6b3d28fb`. Scope depth remains as stated above.

| File | SHA-256 |
| --- | --- |
| `ProofProject/LowerBound.lean` | `67de5739e389480ef546d9139f236c3925c02aa0964f3553a0d5ffdb0305c687` |
| `ProofProject/SourceBoundaryEstimate.lean` | `a009d41818421ab36b8e5d72796aa815f0868e4898133de87b2f5701d3ebf6b9` |
| `ProofProject/SourceBoundaryLower.lean` | `32b4ac28b9d2cd1a3f4bade1fa13d768159c88b37edc51fbac02289f0b125fe1` |
| `ProofProject/FiniteModelLower.lean` | `ce6b00f57141c642359f15d78f9540b5cc05227bb9fb46866ac1c147af510d8c` |
| `ProofProject/Endpoint.lean` | `a764ec9738de7bf9991304081baeca53afdd642830d896734c382808edef0e7c` |
| `ProofProject/HilbertULift.lean` | `3a1eb5a4c0f42996561c575d5acb656e90160ff72576179f80a7725d42f3ba04` |
| `ProofProject/SourceWeightFactor.lean` | `a26e3f9c749aea37e854023183cea8b6ed7be1e732670b77e5e606c91479be92` |
| `ProofProject/CoefficientSquare.lean` | `3a4bdf9d2a9df8e4a5b30fcbd903fc8c57b0e13fa78892d54b47df17380df940` |
| `NUMERICAL_TARGETS.md` | `8f02633f51ae3516e23ace8000310532bc28909d853c99a9d024a6e32367c901` |
| `../../../docs/lean/REVIEW.md` | `d967ddce620d4e754e2f9c25548f30cb537f76f4ddcf8ecf2574945bcd332553` |
| `../README.md` | `5c7f922fe777090b92c593447142ea4135a6be54914f11cf081397c017ae640f` |
| `README.md` | `ccca400db3dbe6aceaac573628dccce70d5403bcf1f75425e6aa8b17016c3e8d` |
| `LICENSE` | `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30` |
| `Challenge.lean` | `b8a14a878b4a8aced61b0de4f8f5d90b2c488e9d5c63a7748a9a84092982b4d6` |
| `Solution.lean` | `cea58f6ca9fa54d0a8951e356f38d42f51e95ff6bdb101039e94303c91d7567c` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lakefile.toml` | `95458a5f2e532fd06d67e5c774020f7d017036b4470c4a45d7cbca203464901d` |
| `lake-manifest.json` | `0acce5272fbb94ad70c33f39f1d7832bd17fa7e6fefb3b5076514d38e9b14502` |
| `../MF-17-research-handoff.pdf` | `40bb30b1d087625d0b434d34ce8380d96081095c840ce6bd1f95cea9d280dec4` |
| `ProofProject/Definitions.lean` | `d6ca7cb8cd5ab8ffba64ad903c55e2153bb505d298616d6d1bac97e68767204a` |
| `ProofProject/Envelope.lean` | `5d0a12997b398ff712112514082992691c35a724b9e9f8e15992218d128dc93a` |
| `ProofProject/SharpGrowth.lean` | `2e592957ed0f13c37c430adaf7e775efa181ed955dcd17f01458ac3771b7a877` |
| `../problem.tex` | `836856a8712aa051c3687c085c88804bc481927487b7ed656c451f1820fe6967` |


## Final incorporation verdict — 2026-09-30

Reviewer: **Aquinas, independent AI reviewer (task 01a0f233-bfc7-7e03-a460-93aeb5dd43d2)**. This is a limited retrospective follow-up on the two documentation objections above. I directly read the revised `NUMERICAL_TARGETS.md` and project `README.md`, and inspected `formalization.yaml`'s adaptation/fidelity descriptions. I did not rely on another review or on a build claim.

**Verdict: approve incorporation of these documentation fixes. Both objections are resolved.** This supersedes the earlier requested-changes verdict for the reviewed statement-fidelity, lower-bound, endpoint, and attribution remit, subject to the original checked scope and limitations. The source-level approval of all five Challenge signatures stands. No concrete objection from this report remains open.

- **Objection 1 resolved:** the new “Adaptations of the manuscript proof” section displays both the implemented scalar factor and the manuscript's different one-sided factor, identifies the two-component manuscript construction, and explicitly records the scalar monomials, alternating-sign witness, replication, separate metric perturbation, dimension, margin, and separation changes. It identifies the inherited comments being corrected. The README opening now calls the arguments adapted and links this explanation; the manifest fidelity description records the same boundary. The note correctly relies on the formalized factor's own branch and boundary estimates rather than an unproved identification with `h(z)/h(-z)`. For the independently proved replacement route reviewed here, that clarification is sufficient; a new ratio-identification theorem is not required.
- **Objection 2 resolved:** the note explicitly contrasts `(M^4+1)/(M^2-1)` with manuscript `(S.6.6)`'s `2*M^4/(M^2-1)`, and `1/(4B)` with `(S.6.4)`'s `1/(8B)`. It calls both proved refinements and explicitly corrects the named inherited exact-source attributions. This implements the correspondence-note remedy allowed in the original review while preserving the proof comments and executable source bytes.

I recomputed the entire 221-file solution-source aggregate using the procedure above: it remains `e207a749abbd7ca013ebd3faf4071b0563fd547618c08672a15b918f9ea56170`. The individual Challenge and Definitions digests also remain unchanged. Thus this follow-up incorporates explanatory corrections into the existing review; it does not replace that review with a fresh proof audit or require reopening the frozen mathematical contracts.

The following digests identify the follow-up inputs. The documentation entries supersede their earlier byte identifiers for this incorporation verdict; the earlier entries remain as historical evidence of the original review. The manifest digest identifies the file containing the inspected fidelity descriptions, not approval of every unrelated metadata or verification field.

| File | SHA-256 |
| --- | --- |
| `NUMERICAL_TARGETS.md` | `8404a7ca5da860ba7298fcf540a69887c74e0da3fce469949885428d5ea83bc3` |
| `README.md` | `686f2f5d66cea33026c339ce33ccc3adc59e0de2f6aeff9ef90ed38898d50869` |
| `formalization.yaml` | `7ef5faa88d1f9dbb26bda9fdbf6fde4cd63ac900a3c812255193271887152c1e` |
| `Challenge.lean` | `b8a14a878b4a8aced61b0de4f8f5d90b2c488e9d5c63a7748a9a84092982b4d6` |
| `ProofProject/Definitions.lean` | `d6ca7cb8cd5ab8ffba64ad903c55e2153bb505d298616d6d1bac97e68767204a` |

I executed no Lean, Lake, axiom audit, or Comparator and inspected no execution logs in this follow-up. Runtime verification remains parent work. This approval is not human peer review, does not extend the original mathematical proof scope, and does not certify a `Lean verified` or `Solved` status. Only this review report was modified.
