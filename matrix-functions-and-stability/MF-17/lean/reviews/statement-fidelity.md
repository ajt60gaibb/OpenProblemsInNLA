**MF-17 retrospective statement-fidelity and scope review**

Date: 2026-09-30 (UTC). Reviewer: Ptolemy, independent AI reviewer (task 01a0f233-bf7a-77d1-8348-b7d902c946c3). I did not implement these proofs. This is an independent AI source review, not human peer review, not a pre-implementation approval, and not a Lean verification certificate.

**Verdict: APPROVE statement fidelity and scope for the source bytes identified below.** I found no material mismatch between the canonical original problem, Part VI Theorem S.1.1, the five Challenge statements, and the corresponding declarations exposed by Solution. No statement changes are requested. This verdict is limited to the inspected statement boundary and supporting bridges; it does not certify the mathematical correctness of the full imported proof.

The review follows the retrospective fidelity-and-scope responsibility in `docs/lean/REVIEW.md`. I read the canonical README's original statement separately from its solution-claim text, `NUMERICAL_TARGETS.md`, all of Challenge and Solution, and the source files listed below. I extracted PDF pages 43–45 with `pdftotext -layout`, including Theorem S.1.1 on printed page 42 and the following two printed pages. I did not review the complete manuscript proof. No Lean, Lake, Comparator, or transitive axiom audit was run; no build or verification logs were inspected. The parent handles the build. The protocol's mechanical gates, including Challenge type-checking, are not discharged by this report.

**Comparison with the mathematical target.** The original normalized class is all complex Hilbert-space C₀ semigroups with `‖T(s)‖ ≤ M exp(-s)` for every `s ≥ 0`, with possibly unbounded generators. The requested object is the supremum of `‖exp(t A⁻¹)‖` over that class. Theorem S.1.1 supplies the additional candidate answer

`L(t) = log(log(t + exp(exp(1))))`, `α(M) = (2/π) arccos(1/M)`,

with matching positive multiples of `L(t)^α(M)` for every sufficiently large time, at each fixed `M > 1`. It also states the contractive endpoint and sufficiency of finite-dimensional lower witnesses. Those are precisely the mathematical conclusions presented at the formal boundary. The theorem's explicit `c_M ≤ C_M` is not a separate conjunct of `sharp_growth`, but follows from its two inequalities at `t = t₀`, since `L(t₀)^α(M) > 0`. Requiring `t₀ > 0` instead of merely a finite threshold is an equivalent harmless restriction for an eventual estimate: increase the threshold if needed.

**Full generator domain, inverse, and exponential.** In `ProofProject/Definitions.lean:19`, `StableSemigroup` requires complex continuous linear operators, identity at zero, the semigroup law for all nonnegative pairs, strong continuity of every vector orbit on `[0,∞)`, and the exact normalized bound. Strong continuity is not replaced by operator-norm continuity. Defining `op` on all real numbers imposes no condition on negative times; any semigroup on `[0,∞)` admits such an extension, and `GeneratorGraph` only uses the right derivative at zero.

`GeneratorGraph` at line 30 is the entire relation `HasDerivWithinAt (fun s => T.op s x) y (Ici 0) 0`. In a normed space this is the strong right derivative defining the generator. There is no user-selected subdomain, bounded generator parameter, differentiability of every vector, or additional certificate restricting admission. `GeneratorGraph.unique` explicitly uses uniqueness of differentiation within `Ici 0`. The canonical dense-domain property is implicit in the standard generator characterization of a C₀ semigroup; I did not find or certify a separate formal density theorem in the inspected files. Its absence from the structure does not exclude any original generator or allow a chosen restriction of its domain.

`IsGeneratorInverse` at line 34 is the biconditional, for **all** `x,y`, `GeneratorGraph T x y ↔ B y = x`. Its reverse implication gives `A(B y) = y` for every vector `y`; its forward implication gives `B(A x) = x` on the complete generator domain. This is stronger than merely asserting an inverse on a convenient core. `Generator.lean` also identifies `range B` with this domain and derives injectivity and uniqueness.

The inspected inverse bridge has the correct sign: `laplaceInverse x = -∫₀∞ T(s)x ds`. Integration is vectorwise, so the construction does not assume operator-valued Bochner measurability or separability of the entire Hilbert space. `StableSemigroup.laplaceInverse_graph` in `LaplaceGenerator.lean` supplies the right inverse; `GeneratorGraph.laplaceInverse_eq` in `GeneratorOrbit.lean` supplies the left inverse on every graph pair; `StableSemigroup.isGeneratorInverse_laplaceInverse` in `InverseGenerator.lean` combines them. `stableSemigroup_hasGeneratorInverse` in `Solution.lean` calls that bridge. These observations check the meaning and source-level connection, not independent kernel acceptance of these proofs.

`inverseEvolution` at line 38 is `NormedSpace.exp ((t : ℂ) • B)` in the algebra of complex continuous linear endomorphisms. For the complete spaces quantified by the targets, this is the usual operator-norm power-series exponential. It is not a scalar surrogate or a separately postulated evolution. The inspected `BoundedGenerator.lean` identifies the entire generator graph for exponential semigroups as `y = A x` and transports algebraic two-sided inverses into this same relation for the finite-dimensional construction.

**Spaces, universes, and quantifier order.** `attainableNorms` existentially quantifies a type `H : Type u`, its normed additive group, complex inner product, completeness instance, semigroup, and bounded inverse. No finite-dimensionality, separability, nontriviality, or fixed model of Hilbert space occurs in this definition. The upper estimate `SharpUpperBound.exists_inverseEvolution_sharp_upper` explicitly selects `C` after `M` and before **every** such `H`, `T`, `B`, and positive time. Its hypotheses contain only stability and the actual inverse relation, not the desired growth estimate.

The five declarations are polymorphic in an arbitrary universe `u`; the envelope is a set of real values, defined by existential quantification over the spaces in that universe. Thus the precise formal claim is made separately in each fixed universe. It is not a single supremum over a proper class of all universes, nor an explicitly stated equality of envelopes across universes. This is the documented foundational interpretation, not a finite-dimensional or separable restriction. Constants are uniform over spaces within that arbitrary universe; the theorem signatures alone should not be advertised as a cross-universe equality or a simultaneous choice of constants over universes. `ScalarExamples` uses `EuclideanSpace ℂ (ULift.{u} Unit)` to supply nontrivial examples in each universe. `SourceBoundaryLower` and `HilbertULift` explicitly lift the lower-model family and preserve its relevant norms and boundary estimates.

In `sharp_growth`, the order is `∀ M > 1, ∃ c C t₀ > 0, ∀ t ≥ t₀`, followed by the two inequalities for the envelope. The space is hidden only by the correctly defined supremum; it is not fixed before the constants. In `finite_dimensional_lower`, the order is `∀ M > 1, ∃ c t₀ > 0, ∀ t ≥ t₀, ∃ H,T,B,...`. Hence the finite dimension, Hilbert space, and generator may depend on time. There is no assertion of a single finite-dimensional generator realizing unbounded growth at every late time. The inverse-existence target quantifies each admissible `T` before a unique `B`, independently of any time parameter. The boundedness and endpoint targets cover every nonnegative real time, including zero.

**Exact M, exponent, clock, and witness bridge.** The admissibility bound is the same real `M` in both `attainableNorms` and `HasFiniteWitness`; “exact M” means the prescribed upper budget `≤ M exp(-s)`, not that the best possible semigroup constant must equal M. No `M + ε`, asymptotic replacement of M, or loss in the exponent appears in the five conclusions. `growthExponent` is exactly `(2 / Real.pi) * Real.arccos (1 / M)`, and `growthLog` uses natural logarithms with the exact shift `exp(exp(1))`. Since the exponent is real, the power is real exponentiation. `GrowthRate` establishes `L(0)=1`, `L(t)≥1` for `t≥0`, and `0<α(M)<1` for `M>1`, avoiding zero/negative-base ambiguities on all target times.

The top-level lower declaration has no undisclosed boundary-estimate hypothesis. `LowerBound.finite_dimensional_lower` supplies it using `sourceBoundaryConstant_pos` and `sourceUnitFamily_hasBoundaryEstimate`, then invokes `finite_dimensional_lower_of_source_boundary`. The inspected boundary/sign-model and finite-witness interfaces retain M. `DiscreteLower.finiteWitness_lower_of_discrete` and `Rescaling.HasFiniteWitness.mono_time` transport positive-time peaks to every sufficiently large time. The rescaling is acceleration by `c ≥ 1`, which preserves `M exp(-s)` because `M exp(-cs) ≤ M exp(-s)`; the inverse scales by `c⁻¹`, so its exponential at the new observation time is unchanged. This addresses the potential mismatch between a subsequence lower bound and the requested all-large-times lower bound. The imported analytic estimates and full finite-model construction remain outside this statement review's proof-correctness coverage.

**Real supremum and endpoint edge cases.** `growthEnvelope` is real `sSup`, not an extended-real supremum. In isolation, such a definition would not establish the intended envelope for an empty or unbounded set. The inspected bridges address both obligations in the target regime:

- `ScalarExamples.attainableNorms_nonempty` provides an actual nontrivial scalar example for every `M ≥ 1` and real t. For `a ≥ 1`, the generator `-a I` gives attainable value `exp(-t/a)`.
- `Envelope.attainableNorms_bddAbove` bounds every value by `exp(t*M)` for `M ≥ 1`, `t ≥ 0`, through the inverse estimate `‖B‖ ≤ M`. This is independent of the sharp asymptotic estimate.
- `LowerBound.HasFiniteWitness.le_growthEnvelope` applies `le_csSup` with that boundedness. `SharpGrowth.growthEnvelope_sharp_upper` applies `csSup_le` with nonemptiness and a bound on every member. Thus the inspected envelope transfers do not rely on default behavior of real supremum outside its meaningful cases.
- The zero Hilbert space is permitted. Its operator norm is zero, including the identity; the inspected general estimates use `norm_id_le` rather than the nontrivial-space equality `norm_id = 1`. Adding zero to the attainable set cannot change this envelope, which is already at least one.
- For fixed t, `exp(-t/a) → 1` as `a → ∞`. The scalar limit supplies `G_M(t) ≥ 1` once boundedness is known. At `M=1`, the dissipativity argument in `Contractive.lean` bounds each inverse evolution by one, and `Endpoint.contractive_envelope` combines this with the scalar supremum lower bound. Equality of the supremum does not claim attainment at positive t. `Endpoint.growthEnvelope_zero` also handles `t=0`, where a nontrivial scalar space attains one.

No target asserts an envelope interpretation for `M<1` or a sharp estimate at negative time; total real definitions outside the stated parameter range do not enlarge the claims.

**All five Challenge/Solution declaration comparisons.** All names below are in namespace `ProofProject`. I compared the complete written signatures, including binders, inequalities, universe annotations, and instance requirements. A Python text comparison of each signature through `:= by` also returned five matches after removing whitespace and normalizing the sole binder-name change `hM`/`_hM`. This is a source-text check, not an elaborated-type or kernel check.

| Challenge declaration | Actual Solution-side declaration | Result |
| --- | --- | --- |
| `stableSemigroup_hasGeneratorInverse`, line 10 | `Solution.lean:19` | Same `M ≥ 1`, arbitrary complete complex Hilbert space, T, and unique bounded inverse; only `hM` is renamed `_hM`. |
| `attainableNorms_bddAbove`, line 15 | `ProofProject/Envelope.lean:43` | Same `M ≥ 1`, `t ≥ 0`, and `BddAbove (attainableNorms.{u} M t)`. |
| `sharp_growth`, line 19 | `ProofProject/SharpGrowth.lean:25` | Same positive constants/threshold, universal late-time quantifier, exact rate, and two inequalities. |
| `finite_dimensional_lower`, line 26 | `ProofProject/LowerBound.lean:14` | Same constants-before-time order and `HasFiniteWitness.{u}` with unchanged M and rate. |
| `contractive_envelope`, line 32 | `ProofProject/Endpoint.lean:20` | Same nonnegative-time endpoint `growthEnvelope.{u} 1 t = 1`. |

Solution directly declares only the inverse theorem; its `ProofProject.Helpers` import explicitly imports the modules declaring the other four. Challenge imports only Definitions and contains five deliberate `sorry` placeholders. I have not treated those placeholders as evidence for any mathematics or substituted Challenge for Solution in this comparison. The public targets impose no extra assumptions such as an admissible boundary certificate, a supplied sharp estimate, or a finite-dimensional upper-bound hypothesis.

**Scope limits.** This report approves the claimed asymptotic order, not a limiting leading coefficient, optimal constants, estimates uniform as `M ↓ 1`, a single extremizing generator, manuscript Part IX, or a uniform bound on witness dimension. The original problem asks for an order, so those omissions are appropriate. I did not independently reconstruct the analytic upper/lower arguments, read every imported module or pinned Mathlib definition, check toolchain reproducibility, inspect compiled declarations, run a full dependency/axiom audit, or establish that any theorem compiles. I did not run the two-reviewer workflow or assess other reviewers. Mathematical proof correctness, build acceptance, Comparator acceptance, and repository promotion remain separate decisions. No source or remote was changed; this report is the only file written by this reviewer.

**Exact reviewed files and byte identifiers.** Paths in the first table are relative to `/Users/april/Documents/overleaf/MF-17/OpenProblemsInNLA`; paths in the second are relative to its `matrix-functions-and-stability/MF-17/lean` directory. Hashes are SHA256 of whole-file bytes, even when the inspection was limited to the stated excerpt. They identify review inputs, not verification artifacts. Documentation may subsequently change in the parent task; this approval attaches to these bytes.

Post-review documentation note (2026-09-30): The user reports that the canonical README prose was updated to link the local Lean source; the original mathematical statement and all reviewed Lean sources are unchanged. Approval of the original statement is unchanged. The README digest below identifies the version originally reviewed, not the later documentation revision. Existing source digests are retained and were not recomputed for this attribution/documentation update.

**Canonical inputs and protocol**

| File | Inspection scope | SHA256 |
| --- | --- | --- |
| `docs/lean/REVIEW.md` | Entire protocol | `d967ddce620d4e754e2f9c25548f30cb537f76f4ddcf8ecf2574945bcd332553` |
| `matrix-functions-and-stability/MF-17/README.md` | Entire file; original statement is canonical | `f6c51ef1deef07bbd10d6d72251ed8467bbd17b235a5adfc9e04875241ce9daf` |
| `matrix-functions-and-stability/MF-17/MF-17-research-handoff.pdf` | PDF pages 43–45 only; printed pages 42–44 | `40bb30b1d087625d0b434d34ce8380d96081095c840ce6bd1f95cea9d280dec4` |
| `matrix-functions-and-stability/MF-17/lean/NUMERICAL_TARGETS.md` | Entire file | `8f02633f51ae3516e23ace8000310532bc28909d853c99a9d024a6e32367c901` |

**Formal source inspected**

| File | Inspection scope | SHA256 |
| --- | --- | --- |
| `Challenge.lean` | Entire file | `b8a14a878b4a8aced61b0de4f8f5d90b2c488e9d5c63a7748a9a84092982b4d6` |
| `Solution.lean` | Entire file | `cea58f6ca9fa54d0a8951e356f38d42f51e95ff6bdb101039e94303c91d7567c` |
| `ProofProject/Definitions.lean` | Entire file | `d6ca7cb8cd5ab8ffba64ad903c55e2153bb505d298616d6d1bac97e68767204a` |
| `ProofProject/Generator.lean` | Entire file | `cdf5d8aa982564c674f8418265616f19e77e95763a31c4eef5b101a79419fa21` |
| `ProofProject/Laplace.lean` | Entire file | `f8074ad3c66b577ecf25bf3da1bce9b630149da224975a236ffe840411b16fd8` |
| `ProofProject/LaplaceGenerator.lean` | Entire file | `19e9ecbf6f89578131364cbadbc540b8858cb3d318dbc71eb7b74156b41e5151` |
| `ProofProject/GeneratorOrbit.lean` | Entire file | `a07474c85b4ed49cd79005010621e301c72b3bec52eade139708ad2636dbba70` |
| `ProofProject/InverseGenerator.lean` | Entire file | `5f13f51d4d7a66d1d4f2220873c29cb11eb8222dae389cc3795c1beda57b0693` |
| `ProofProject/Envelope.lean` | Entire file | `5d0a12997b398ff712112514082992691c35a724b9e9f8e15992218d128dc93a` |
| `ProofProject/ScalarExamples.lean` | Entire file | `7728f68bb1cacb3268aa3155218adab91274758d4d1988681fd410fae6519e60` |
| `ProofProject/Endpoint.lean` | Entire file | `a764ec9738de7bf9991304081baeca53afdd642830d896734c382808edef0e7c` |
| `ProofProject/Contractive.lean` | Entire file | `1027b7dce298af0d62c39c6b8a833c4f243b1d2c32730dec3230ba3c271cc92c` |
| `ProofProject/LowerBound.lean` | Entire file | `67de5739e389480ef546d9139f236c3925c02aa0964f3553a0d5ffdb0305c687` |
| `ProofProject/SharpGrowth.lean` | Entire file | `2e592957ed0f13c37c430adaf7e775efa181ed955dcd17f01458ac3771b7a877` |
| `ProofProject/Helpers.lean` | Entire file | `9cdb9bd8af2290ba4354fec5eb41dbe30e493a253647892ee0d068e18c63f682` |
| `ProofProject/GrowthRate.lean` | Entire file | `b0311c38cd6e9c1ca8b85a44ce709472828be4dc6410c737e2fd9df800347311` |
| `ProofProject/SharpUpperBound.lean` | Entire file | `fc208f2160dec4df29c6430a0d26a7a1387ad5a9de87a90c1e4b73050ae5ab31` |
| `ProofProject/SourceBoundaryLower.lean` | Entire file | `32b4ac28b9d2cd1a3f4bade1fa13d768159c88b37edc51fbac02289f0b125fe1` |
| `ProofProject/HilbertULift.lean` | Entire file | `3a1eb5a4c0f42996561c575d5acb656e90160ff72576179f80a7725d42f3ba04` |
| `ProofProject/BoundaryLower.lean` | Entire file | `2f1ec7c8b635678c689d4fdbbe92b16991a0cf5425a5c19035dc5f1ef820d9b5` |
| `ProofProject/FiniteModelLower.lean` | Entire file | `ce6b00f57141c642359f15d78f9540b5cc05227bb9fb46866ac1c147af510d8c` |
| `ProofProject/FiniteModelWitness.lean` | Entire file | `78cd3d599cde42ac230b9607e280c78ca5eb996b997861452a5ef915ce904c5c` |
| `ProofProject/BoundedGenerator.lean` | Entire file | `250d51462767194300fc37298b4329eb6772977c050553209e9fe6b4b7805209` |
| `ProofProject/Rescaling.lean` | Entire file | `dc0f13c557d7e5390db9de9e7edd375f48ddff91e2494ed885d804d4ecc03776` |
| `ProofProject/DiscreteLower.lean` | Entire file | `5f1b5a74dfc0191700764c9b1df94553b15b8bbbd1d8ea328b50702057db3f9e` |
| `ProofProject/SourceBoundaryEstimate.lean` | Declaration listing and lines 150–end; chiefly sourceUnitFamily_hasBoundaryEstimate | `a009d41818421ab36b8e5d72796aa815f0868e4898133de87b2f5701d3ebf6b9` |

Procedural instructions also read (not mathematical evidence):

- `/Users/april/Documents/overleaf/MF-17/OpenProblemsInNLA/AGENTS.md` — SHA256 `d7e27520acdcb0edacebf965b56f5b1e3fb0205d83da45a7fa021e0bedb80162`.
- `/Users/april/Documents/AGENTS.md` — SHA256 `9d219a76f19835f563515b0909d98e8a1d30e5a55b2fa31ccd7a05d2cbc4c9db`.
