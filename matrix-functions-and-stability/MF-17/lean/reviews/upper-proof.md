# MF-17 upper-bound proof and trust review

Date: 2026-09-30. Phase: retrospective final source review.

Reviewer: Hume, independent AI reviewer (task 01a0f233-bfa4-7061-b05c-302eac6905ac). I am a nonimplementing reviewer: I did not implement or change the proof. This is not human peer review. I executed no Lean builds, elaboration probes, Comparator runs, or `#print axioms` commands, and inspected no build/axiom/Comparator logs. The parent process is responsible for those mechanical gates.

Source project: `/Users/april/Documents/overleaf/MF-17/OpenProblemsInNLA/matrix-functions-and-stability/MF-17/lean`. All project paths below are relative to this directory unless stated otherwise. Only this report was written; no remote actions were taken.

**Verdict: APPROVE the inspected upper-bound argument at source-review scope. No material mathematical or trust defect was identified in the inspected argument.** This is not certification of the entire Solution proof closure or a claim that these bytes compile. The coverage boundary and outstanding verification gates below are part of the verdict.

I read `docs/lean/REVIEW.md`, `NUMERICAL_TARGETS.md`, the canonical problem README, and `Challenge.lean`. The reviews directory was empty when initially inspected; no earlier substantive referee findings were available there to resolve. README claims were not evidence for proof correctness.

## Material audit findings

### 1. Full generator, genuine target, and nonvacuous envelope

`Definitions.lean:19–39` defines the semigroup by its law, strong continuity on nonnegative times, and the actual bound `M * exp(-s)`. `GeneratorGraph` is the full `HasDerivWithinAt` graph at zero on `Ici 0`, and `IsGeneratorInverse` is the equivalence `GeneratorGraph T x y ↔ B y = x` for **all** vectors `x,y`. There is no chosen subdomain, bounded-generator hypothesis, finite-dimensionality, separability, or assumed growth estimate in these definitions. `inverseEvolution` is the standard operator exponential.

The inverse premise is discharged for every stable semigroup: `Laplace.lean` establishes orbit integrability and constructs the bounded negative Laplace integral; `LaplaceGenerator.lean:48` proves its right-inverse graph property; `GeneratorOrbit.lean:52–80` integrates every generator orbit and proves the left inverse; `InverseGenerator.lean:16–27` assembles existence and uniqueness. `Solution.lean:19` uses that construction. Right derivatives suffice by the pinned Mathlib FTC statement inspected below. This covers unbounded generators through their full graph.

`ScalarExamples.lean:83–93` constructs admissible scalar semigroups in an arbitrary universe and proves the attainable set nonempty. `Envelope.lean:34–47` independently bounds every attainable value by `exp(t*M)`. Thus the real supremum is not exploiting an empty or unbounded set. In `SharpGrowth.lean:20`, `csSup_le` needs only nonemptiness and the exhibited upper bound: its Mathlib proof constructs `BddAbove` from that same bound. The absence of a separate boundedness argument at this particular call is sound.

The zero space causes no normalization exception: the final assembly uses `norm_id_le`, not `norm_id = 1`. Nontrivial scalar witnesses independently supply nonemptiness.

### 2. Exact M and quantifier order survive the assembly

`SharpUpperBound.lean:23–37` selects `Cosc`, the fixed Bessel coefficients, the fixed remainder, and
`C = 1 + (‖cPlus‖ + ‖cMinus‖) * Cosc + M * ∫ u, ‖h u‖`
before introducing the Hilbert space, semigroup, inverse, or time. Its statement is
`∀ M > 1, ∃ C > 0, ∀ H T B, IsGeneratorInverse T B → ∀ t > 0, ...`.
It proves the stronger all-positive-time upper bound.

`OscillatorySemigroup.lean:22–61` proves that `exp(u/t) T(u/t)` has exactly bound `M`; `BoundedSemigroup.ofStableRescale` carries that proof without an extra structural premise. Strong continuity of adjoints is proved in `AdjointSemigroup.lean` by dense-range approximation, rather than assumed. Kernel integration takes place after applying to a vector, avoiding an operator-norm measurability restriction on arbitrary Hilbert spaces.

The delicate exponent loss is addressed in code, not just documentation. `ApproximateSynthesis.lean:60–113` temporarily has exponent at `M+ε`, then invokes `GrowthExponentPerturbation.growthExponent_rpow_perturbation` for `ε ≤ 1/n`. The latter proves the power ratio is at most `exp(growthExponentLipschitzConstant M)`. `SourcePieceSynthesis.lean:33–60` includes the factor `sqrt(M+1)` in the error budget and uses `1/m`; `SeparatedOperatorSum.lean:56–77` handles retained length `n ≤ m`, including zero length. There is no fixed enlargement of M left in the final exponent.

`SharpGrowth.lean:14–33` transfers the uniform bound to the envelope and combines it with the lower theorem's positive threshold. Constants precede time. The universe is fixed but arbitrary, as stated in NUMERICAL_TARGETS; no single theorem quantifies over Lean universes as objects. The sharp upper theorem assumes `M>1`, and does not purport to prove the contractive endpoint.

### 3. The actual inverse exponential is linked to the actual Bessel series

`BesselKernelSeries.lean:20–51` defines
`b(u) = Σ (-1)^n u^n / (n! (n+1)!)`
and proves absolute convergence, rather than using a formal or potentially divergent tsum.

The live representation path is:

`Laplace inverse → RescaledResolventInverse → GammaConvolution / GammaResolventPowers → GeneratorInversePowers → GeneratorExponentialSeries → InverseExponentialKernel`.

I inspected the gamma normalization, shape-one convolution, nonnegative support, positive change-of-variable Jacobian, and both signs in the exponential series. The normalized resolvent at rate `1/t` is `-B`; its gamma powers multiplied by `(-t)^(n+1)/(n+1)!` sum to `inverseEvolution B t - 1`. `GammaKernelSeries.lean:77–107` proves their scalar sum is **minus** the damped Bessel kernel. Consequently `InverseExponentialKernel.lean:38–67` obtains `1 - kernelOperator`, with the correct sign and scaling.

The crucial absolute majorant is established before the asymptotic: `GammaKernelSeries.lean:48–74,125–158` proves the integral of the pointwise norm series equals `exp(t)-1`, which is positive for `t>0`. It then obtains genuine integrability and dominates the Bessel kernel. `SemigroupKernelSeries.lean:31–76` supplies operator summability, vector-integral summability, and the series/interchange argument. `SemigroupKernelConvolution.lean:40–66,114–139` supplies the integrable product bound needed for Fubini and uses the semigroup law only at nonnegative times.

The uses of `Integrable.of_integral_ne_zero` in `GammaKernel.lean:80` and `GammaKernelSeries.lean:137` are not total-integral loopholes. The pinned Mathlib definition returns zero on nonintegrable functions, and the inspected lemma is its contrapositive. The code first derives the nonzero integral identities from gamma/exponential series facts. No Bessel decay or sharp semigroup estimate is assumed in this argument.

### 4. Bessel asymptotic and fixed L¹ remainder are proved independently

`BesselKernelODE.lean:80–107` justifies differentiation with a summable factorial majorant on a bounded open interval. The coefficient recurrence gives `u b'' + 2 b' + b = 0` at line 175. `BesselOscillator.lean` proves, for `v(r)=r^(3/2)b(r²/4)/2`, the system `v'=p`, `p'=-v+3v/(4r²)`.

`OscillatorEnergy.lean` differentiates `(v²+p²) exp(3/(4r))` to a nonpositive square and obtains a uniform bound on `r≥1` without dividing by energy. `OscillatorAsymptotic.lean:64–109` bounds the derivatives of the rotating coefficients by an integrable inverse square. `DerivativeTailLimit.lean:21–50` proves their limits exist and have error at most `C/r`; limit existence is not an input. `BesselAsymptotic.lean:48–109` converts this into the two-phase `u^(-3/4)` model with `O(u^(-5/4))` error. Allowing zero leading coefficients is harmless for this upper bound.

`SourceBesselRemainder.lean:87–120` constructs the actual difference, handles `(0,64]` by continuity, and handles the tail by the integrable `u^(-5/4)` estimate. The cutoff equals one below 32 and zero above 64; clipping the model's power at 32 is proved to leave the cutoff product unchanged. At nonpositive u all supported kernels vanish. The coefficients and remainder are chosen before **every** damping time in `exists_bessel_tail_decomposition` (line 143). Positive damping decreases the remainder's norm, so its contribution is the time-independent `M‖h‖₁`.

### 5. The oscillatory-tail interface is not left as an assumed main estimate

`OscillatoryTailBound.lean:23–39` passes a proved uniform finite-sum estimate through strong convergence. `SourcePieceLimit.lean:55–71,164–190` proves the cutoff telescope eventually agrees pointwise with the genuine tail kernel, and uses an integrable exponential majorant to pass vector integrals to the limit. No operator-norm convergence or unproved representation is assumed.

The finite-sum route is explicit: source amplitude derivative bounds → actual piece bounds and resolvent deletion/retention → commuting separators → finite synthesis with reciprocal error budget → logarithmic removal and parity split → time clock and damped tail. I inspected the caller/callee matching in the files marked R below. `SourcePieceClock.lean` bounds the clock index by a constant times the exact double logarithm and puts its scale beyond t. `SourcePieceDampedTail.lean` bounds the remaining finite damping sum by one. These bounds hold uniformly in positive time.

Several intermediate declarations intentionally take strong analytic premises. They are discharged on the inspected live path:

- `HasSharpTailGeometry` and `HasSharpOuterPolynomialEstimate` are explicit interfaces, not axioms. `SharpTailGeometry.lean:23–35` proves them from `outerPolynomial_interior_estimate`, `outerPolynomial_boundary_bound`, and the finite-family polynomial reduction. `SeparatedOperatorSum.lean:50` passes this proved geometry to the conditional factor-synthesis theorem.
- `SourceOscillatoryOperator.lean:99–108` supplies the finite Fourier reconstruction's scalar budget using `exists_sourceScalarBudget_signed`. The latter proves both signs and supplies the frequency-gap hypotheses by case analysis; it does not take a scalar budget as a remaining premise.
- `SourcePieceOperator.lean:119–133` supplies actual amplitude/support/derivative premises. `SourcePieceResolvent.lean:28–54` and `SourcePieceSeparation.lean:88–118` supply the actual resolvent estimates and separators.

This verifies these interfaces are connected to proof bodies. It is **not** an exhaustive mathematical re-review of every lower-level Fourier, Schur/interpolation, polar-factor, or analytic-sector lemma used by those bodies; many are scan-only in the manifest.

## Proof-trust source audit

A recursive local-source import traversal starting at `Solution`, after removing nested block comments, line comments, and strings, found **221 project files, 24,652 lines, and no local import cycle**. All unresolved external module names in that traversal were `Mathlib` or `Mathlib.*`. The explicit `Mathlib` umbrella import makes the external environment much larger than the project closure.

Across all 221 project files, the scan found no code tokens for `sorry`, `admit`, `axiom`, `sorryAx`, `unsafe`, `native_decide`, `implemented_by`, `extern`, `opaque`, `partial`, `run_tac`, `run_elab`, local elaborator/macro/syntax declarations, initialization hooks, `mkSorry`, `addDecl`, `ofReduceBool`, `ofReduceNat`, `trustCompiler`, `Lean.*`, `#eval`, or `#reduce`. This is a lexical/source check, not a computed declaration-level transitive axiom set.

The eight option occurrences were inspected in context: six local `backward.isDefEq.respectTransparency[.types] false` settings and two `maxHeartbeats` increases. They affect elaboration/search resources, not kernel acceptance. No custom proof-producing metaprogram was found in the local closure. Ordinary tactics and noncomputable classical definitions remain subject to the normal Lean/Mathlib trust model.

`Challenge.lean` contains five deliberate `sorry` placeholders and repeats the target names, but **is absent from the Solution import closure**. It is a separately declared library root in lakefile.toml. It must remain a separate statement-comparison input; its placeholders provide no proof evidence.

The configuration pins Lean `v4.33.1` and Mathlib `v4.33.1`; the manifest resolves Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`. A read-only local `git rev-parse HEAD` in the Mathlib checkout returned that same revision. This does not establish cleanliness or integrity of every dependency file or compiled artifact. I inspected only the Mathlib excerpts listed below, not its full transitive source closure, tactics, Lean core, or other package implementations.

The parent's independent clean build, statement comparison, and declaration-level transitive axiom audit must establish that the submitted target declarations elaborate from these sources and have no `sorryAx`, custom axioms, or nonstandard computational trust dependencies. Ordinary foundational axioms such as `propext`, `Classical.choice`, and `Quot.sound` are examples of expected standard trust, **not an axiom-output claim from this review**.

## Coverage and limitations

64 project files were read in full for proof/definition/import-path review (R); six received only the indicated excerpts plus the lexical scan (P); 151 received only import/trust scanning (S). R does not mean every invocation of a library lemma was independently reproved. The complete manifest below names every checked local file and makes these levels explicit.

The lower-bound witness construction and contractive endpoint were not mathematically audited. Reading the final conjunction in SharpGrowth does not approve its lower-bound component. The manuscript PDF and its complete source proof were not inspected, so this is not a full manuscript-fidelity or attribution/reuse review. The canonical README and NUMERICAL_TARGETS supplied the target for the requested upper-bound scope. No claim is made about prior revisions, other workspace copies of the project, or files changed after this snapshot.

No source corrections are requested on the evidence inspected. Remaining mechanical gates and scan-only mathematical dependencies are limitations, not asserted defects.

## Inspected-input byte identities

SHA-256 values below hash actual source bytes. Paths in the first manifest are relative to the source project. R = full source read; P = excerpt read plus scan; S = import/trust scan only. The manifest identifies inputs, not compiled outputs. A final digest comparison found all inspected Lean sources unchanged. The canonical README received concurrent local-link/evidence prose updates; I reread it and recorded its updated hash below. Its mathematical target was unchanged.

| Level | File | SHA-256 |
| --- | --- | --- |
| R | `ProofProject/AdjointSemigroup.lean` | `8a6e3a5443b8cca7414bc53eb09cf45b40f6dd37d87d0beb1c09dc6f7d032fa4` |
| S | `ProofProject/AnalyticCircleMean.lean` | `f71ccd90c3a07d10e28f6420e79ef1db957cf733759d9cc2b410f3a4f78b7140` |
| S | `ProofProject/AnalyticMajorant.lean` | `4ecc3f12b90ef4c5a5769a02f162d3a7564a162c6ed4d5dce2f345ce2cd4e16e` |
| S | `ProofProject/AnalyticSector.lean` | `537ba5957d2769aceee43a95141861b06eb3f5bac8c673eee6b9ecd899eef7d5` |
| S | `ProofProject/AngularPowerIntegrals.lean` | `a3d3c95e4d0d9e3306268f554110d8042ae29fc661743d4e849fcfa9ec265336` |
| S | `ProofProject/ApproximateSeparation.lean` | `18cf8a89720045567727faccdc0a8922d06b2c33758467b61b3e4947916b53b8` |
| R | `ProofProject/ApproximateSynthesis.lean` | `b6ad0b55dc8fdc1e545f8befc5e3f5a1b983322cb36ca4393e71cf1619a757fe` |
| S | `ProofProject/AugmentedSynthesis.lean` | `06c29c1289b1a3607bfef5122f24ef69e38ee42a63109af5772d11712a42002f` |
| S | `ProofProject/AveragedFourierEstimate.lean` | `50042c6ec4b0ee906a96569db09b81817eb37d495cf90bbadac73be538d3dd6f` |
| S | `ProofProject/AveragedFourierFactor.lean` | `f7a9dd03d44b99fbf970bd149f725de6482fee2e6f1b926c593140ee77d988a5` |
| P | `ProofProject/AveragedFourierOperator.lean` | `29690cd3058a02179d0dc743f64016b45f09c98082ad3d3795495b411e6d2b79` |
| S | `ProofProject/AveragingTriangle.lean` | `d90860e47d5b8ba746db181f5b26bfa7020fb144b6358abe9146403a9040fc24` |
| S | `ProofProject/AveragingWindow.lean` | `8f0f8cdcff34e7470617d375d8fb3569c35b155392ab507405d45e0a317546a6` |
| S | `ProofProject/BalancedOperatorFactors.lean` | `bf6dc1bc6101e88989439dcbaf30767f9128ed58453e6d313372e1f4dc0ab3ee` |
| S | `ProofProject/BalancedSeparation.lean` | `f26404c68f199d10e3f96cb73b06c72c4333d060c6c8c3b9ea56b05af5adccc5` |
| S | `ProofProject/BasisEnergy.lean` | `b1b20087c459493f395ea5147675dbe1882ac98a5f5fbbf20381022d40745290` |
| S | `ProofProject/BasisPatterns.lean` | `6bab5c9b96474beda68e2e1c665f6fe8e19c7bab6609e46c9500df0611592c4b` |
| R | `ProofProject/BesselAsymptotic.lean` | `82505ce96827e4f927863b1ce69a5749c99f46235c51afaf353d4907a07ae283` |
| R | `ProofProject/BesselKernelODE.lean` | `7cd08a32fc31d57ed881280fec5f1df95a7f0936a8a7cc1effc516cb234d84ca` |
| R | `ProofProject/BesselKernelSeries.lean` | `73373de1223214a4655b27405dbd9346130133051d86eb2dce14a24fe3bbecc0` |
| R | `ProofProject/BesselOscillator.lean` | `60619f15822fdf7ac0773b2877bdfc3fbedd5fd9f5d53e009061adec69b9c2cc` |
| S | `ProofProject/BoundaryLower.lean` | `2f1ec7c8b635678c689d4fdbbe92b16991a0cf5425a5c19035dc5f1ef820d9b5` |
| S | `ProofProject/BoundedGenerator.lean` | `250d51462767194300fc37298b4329eb6772977c050553209e9fe6b4b7805209` |
| R | `ProofProject/BoundedSemigroup.lean` | `2eae2147f2e54635eec86b9433a7dc7a2f02480f5a146b029b79b105e30e6945` |
| P | `ProofProject/CircleGramPolynomial.lean` | `c14b79811a9fc70afc50b7d45526143dc984b76f8c4b7e3870bb97f4139dfe50` |
| S | `ProofProject/CirclePolynomialDefs.lean` | `bdf43253b22924c00003d45a27c1f484e28e9d985ebb0b7dab77de7d2e3949b8` |
| S | `ProofProject/CirclePolynomialDivision.lean` | `7dcdefd4d7b336249d73de85df7d769f1114f147c9d70dee4cdb58046f26dd7e` |
| S | `ProofProject/CirclePolynomialReflection.lean` | `c25034ae0d1a6ddf829a9af8bac41493a225c6675ab4161a58de2a2d8aebd343` |
| S | `ProofProject/CoefficientSquare.lean` | `3a4bdf9d2a9df8e4a5b30fcbd903fc8c57b0e13fa78892d54b47df17380df940` |
| S | `ProofProject/Contractive.lean` | `1027b7dce298af0d62c39c6b8a833c4f243b1d2c32730dec3230ba3c271cc92c` |
| S | `ProofProject/CosineMargin.lean` | `2cb7c85c80900eced17c7b47327f0062b3b332313ff0e90c83fe2a8cfc61fd2c` |
| S | `ProofProject/CStarSqrtSeparation.lean` | `cc4b97ecb1682fdfeb41bbf4d4afc7f7585dcaab25a840d777bccd4cbaa2b447` |
| S | `ProofProject/DampedPowerDerivatives.lean` | `d1b6008c275f46b91ddd231596977893538f4e0a41fba330d6621e39efd4986f` |
| R | `ProofProject/Definitions.lean` | `d6ca7cb8cd5ab8ffba64ad903c55e2153bb505d298616d6d1bac97e68767204a` |
| R | `ProofProject/DerivativeTailLimit.lean` | `f0fe290e411e49a3510f66baada1a60e9b7be16de4a607fd9dd31f10ce4d46a4` |
| S | `ProofProject/DiagonalOperators.lean` | `0258815f7018d3da12aec287161438c0d5b9cfe23889b897f0352e2704d1af61` |
| S | `ProofProject/DiagonalPeak.lean` | `ba30c4b365230388e669284115b0155a536f5f36ab119c83de6166d8c390b635` |
| S | `ProofProject/DiagonalWitness.lean` | `ccc4ae05dc3a4060894aae0de136f23ffbe0abc10e8439e4b0f02c77976d7ec2` |
| S | `ProofProject/DirichletKernel.lean` | `c5370021574dab024393e257a1dde9a9d8d489b5730eec2faea166367ee9b37c` |
| S | `ProofProject/DiscreteLower.lean` | `5f1b5a74dfc0191700764c9b1df94553b15b8bbbd1d8ea328b50702057db3f9e` |
| S | `ProofProject/DiskSector.lean` | `e64f8346f13e14671be89965f0e2488dd5d31cf30b2939c1f28d772400fc47e7` |
| S | `ProofProject/Endpoint.lean` | `a764ec9738de7bf9991304081baeca53afdd642830d896734c382808edef0e7c` |
| S | `ProofProject/EndpointDeficit.lean` | `756b35cecafa310ad3944c19c6ef56b767473a33ec72b10a05942dc66d34db1b` |
| R | `ProofProject/Envelope.lean` | `5d0a12997b398ff712112514082992691c35a724b9e9f8e15992218d128dc93a` |
| S | `ProofProject/FactorizedSynthesis.lean` | `ce92b2ebd226a6878a17278c7e149ab43407c3c6a4d2913a6e158e99fb26181c` |
| S | `ProofProject/FiniteCircleParseval.lean` | `96366cb0d4f41980a2765a54b3c0e01501d48c9543884b77276b9b1903ada375` |
| R | `ProofProject/FiniteFourierReconstruction.lean` | `11ce011ddfeded966a5d17ede516163f7c68ac7d5b6ca1b7c0b41addd3e2b548` |
| S | `ProofProject/FiniteGeometricError.lean` | `e3c674aa20310fe2650a8fe72777383ce7e82a1362ef8c2702a0cae8b08e5d92` |
| P | `ProofProject/FiniteHankelForm.lean` | `3da92c287d8d83eb33731378b6045656b38b48397591e1c87d946706775c22cc` |
| S | `ProofProject/FiniteLatticeDecay.lean` | `efb2cf3f8a62be256dc5162130c37dbcfec8d7aec1213e79fb15d7540711a631` |
| S | `ProofProject/FiniteModelLower.lean` | `ce6b00f57141c642359f15d78f9540b5cc05227bb9fb46866ac1c147af510d8c` |
| S | `ProofProject/FiniteModelMargin.lean` | `a1f491f4ce01cbb5b3dc6e180dff811ec0bf1831b1d76d0a44c6a6e869c1f538` |
| S | `ProofProject/FiniteModelWitness.lean` | `78cd3d599cde42ac230b9607e280c78ca5eb996b997861452a5ef915ce904c5c` |
| S | `ProofProject/FiniteMomentCoefficients.lean` | `cceebdbd29dd385d8dc1f2545e629a568709cf98d4fbd60faa49a85f23e76ad5` |
| S | `ProofProject/FiniteMomentOrthogonality.lean` | `6e2cca4bd89477fb66f09d6e6c57091d108d7f100e8ee816e4475cc72bc1498d` |
| S | `ProofProject/FiniteParitySplit.lean` | `6dbb313172bf144c2994898f2a82ef556b6509a1479145c87435a2dbb9b05c4b` |
| S | `ProofProject/FiniteSchurInterpolation.lean` | `97015329de57b41b13f2afb1f16f5731a0de2d247754d8c49a6923f9e1ec19c8` |
| S | `ProofProject/FiniteToeplitz.lean` | `0547c3bfab5f2571e30e345b85890da0c5ceaba79683b1a064097f7246c28e19` |
| S | `ProofProject/FourierTailCoefficients.lean` | `a34964ad8d1508598b27b032564e571290f215d989bbeae5389b45147a7595d4` |
| R | `ProofProject/GammaConvolution.lean` | `c7650d7fec9559f295034600adcebc65fdc727eb82516cd1409883941b5545b0` |
| R | `ProofProject/GammaKernel.lean` | `51ea78dc7b955d958e7fdac1da440d0188f8d7277f6e89948c910852d64af370` |
| R | `ProofProject/GammaKernelSeries.lean` | `58b12a0e4c7a76c2f38c063532869973b5f3130966f72337f9f275732d2cd383` |
| R | `ProofProject/GammaResolventPowers.lean` | `28bea111c48417ac7f77ecf44cf3005306a768d3713010d2fafae49b2faa8d5b` |
| R | `ProofProject/Generator.lean` | `cdf5d8aa982564c674f8418265616f19e77e95763a31c4eef5b101a79419fa21` |
| R | `ProofProject/GeneratorExponentialSeries.lean` | `1b09d75bd011dc1afb6606ad5aa6b94147aa296c4d706fd39860df35357ee5bf` |
| R | `ProofProject/GeneratorInversePowers.lean` | `ed8a3f79aeeb0b0c064011d6e950004be8a388c1b361ea3d27c2d3f4d634f3c8` |
| R | `ProofProject/GeneratorOrbit.lean` | `a07474c85b4ed49cd79005010621e301c72b3bec52eade139708ad2636dbba70` |
| R | `ProofProject/GrowthExponentPerturbation.lean` | `e1eaba9bebc8fb833cafc717e4fcdaa8cc805277812176ac233a038c522ef1df` |
| R | `ProofProject/GrowthRate.lean` | `b0311c38cd6e9c1ca8b85a44ce709472828be4dc6410c737e2fd9df800347311` |
| S | `ProofProject/HalfPlaneRadial.lean` | `3bc7675222f90f22b29c0f8cf113cd926694b5d20d02011c7d546aeda989eda8` |
| R | `ProofProject/Helpers.lean` | `9cdb9bd8af2290ba4354fec5eb41dbe30e493a253647892ee0d068e18c63f682` |
| S | `ProofProject/HilbertFourier.lean` | `4ab8a008523ab959e64afdb78e5986712d6b22ca47efa102fe292242cf7058d2` |
| S | `ProofProject/HilbertULift.lean` | `3a1eb5a4c0f42996561c575d5acb656e90160ff72576179f80a7725d42f3ba04` |
| S | `ProofProject/HolomorphicCircleMoments.lean` | `e25d384b0cc788a0ece59b5d6024b0925693e56e7c70574c24d0fbd43adef1d3` |
| S | `ProofProject/IntervalOperatorIntegral.lean` | `b2ecc5d0895578a575b71b004b3a14c77b0be2daa8d884bea445dd5f1622dd62` |
| R | `ProofProject/InverseExponentialKernel.lean` | `1ce3bec26db1c928ed628c4fb14e98a20392c3c26f26329a3cebc853dc916f37` |
| R | `ProofProject/InverseGenerator.lean` | `5f13f51d4d7a66d1d4f2220873c29cb11eb8222dae389cc3795c1beda57b0693` |
| R | `ProofProject/Laplace.lean` | `f8074ad3c66b577ecf25bf3da1bce9b630149da224975a236ffe840411b16fd8` |
| R | `ProofProject/LaplaceGenerator.lean` | `19e9ecbf6f89578131364cbadbc540b8858cb3d318dbc71eb7b74156b41e5151` |
| S | `ProofProject/LaurentCircleProduct.lean` | `10bbc8328f5b5fb30e5496113c7a12dd8014e719fd28dfbe5a90bbc310c24dd3` |
| S | `ProofProject/LowerBound.lean` | `67de5739e389480ef546d9139f236c3925c02aa0964f3553a0d5ffdb0305c687` |
| S | `ProofProject/MetricMargin.lean` | `8d93578b0a9b4a382f963b7a3899cc513ff9c0d8b6848f1a057343485260060d` |
| S | `ProofProject/OperatorBalancedFactors.lean` | `0fcb0d8aafb092ce5dbc436a68104c36aa12639ba6332ee201ee19cb93812037` |
| S | `ProofProject/OperatorPolarExtension.lean` | `07af97380048984133592cfe672fb31400173cacec4b00eaeb71c5881e5da64f` |
| P | `ProofProject/OperatorPolarRange.lean` | `1741f74fa1dc2e9800a90e8827842f0be3997eefe0b6b371dd3586d37c109e94` |
| R | `ProofProject/OscillatorAsymptotic.lean` | `7a184f40e05354228359a8e4121e2cfb9d4ceb99c716e173e2b02d0bf1bf6571` |
| R | `ProofProject/OscillatorEnergy.lean` | `f6dd99c6a2f913e63a974e8faf95f169e486645654c8053d3aaeacdf05659322` |
| S | `ProofProject/OscillatoryCriticalInterval.lean` | `b0d83269126ec02cb34a2cac134bc08796f2f0f1e63a9dfde5405bbdea66137d` |
| S | `ProofProject/OscillatoryFirstDerivative.lean` | `d206069684a0b1be297165bceb3c9e21ceec5a79467ff719832739c115611d1a` |
| S | `ProofProject/OscillatoryIntegration.lean` | `a62a986546875a86562b3d61e0834ac095ee0ea45383470ce434e95d72567f9c` |
| S | `ProofProject/OscillatoryKernel.lean` | `08751545df83bb40075d9a0af026b21eee2059c6c3d12c8debd353e5836ec89b` |
| S | `ProofProject/OscillatoryNonstationary.lean` | `68235197687a6057e223e73acff79ad4ced7ed53256908853d85ba805294b38d` |
| R | `ProofProject/OscillatoryResolventBounds.lean` | `69e82fc4ea9c2e96408acb1987feb973161c657613a3232ac7648d17a56a65d0` |
| S | `ProofProject/OscillatorySecondDerivative.lean` | `2d3bacacf1f9922794d29d9764aa8dbcdd22b4381d3708df18e451b6ff46607d` |
| R | `ProofProject/OscillatorySemigroup.lean` | `6797ee8d8760ba08f0f8019bd6d3a96350d836e3c05d903c6a795eaa91b8b779` |
| R | `ProofProject/OscillatoryTailBound.lean` | `0e47a6bbcf7cb88124d5eceda9c9a1b35afdbd83f8212394d2659c6fa961a5f8` |
| S | `ProofProject/OscillatoryTwiceIntegration.lean` | `5578244539c93ca29e302569ea9fec4ae7a48cd4e21f50aec18ba756a83298f1` |
| S | `ProofProject/OuterCircleWeight.lean` | `e07968b80bb939a43024d347e531d4b26ac90a7d72e748500a71d063b4d07a17` |
| R | `ProofProject/OuterInteriorEstimate.lean` | `046efcb4cbf146810d00e0c88361fa7643d570b3adeec7d8fdcb505312400649` |
| R | `ProofProject/OuterPolynomialBoundary.lean` | `adf811324e51597531c096c8c5c6433c8952d9e79bd46d0b50e10c8991584c67` |
| R | `ProofProject/OuterSectorFunction.lean` | `49d12311dd8ed46c4a2b60d36820b3bb5c23e11ff493f1fe310513f04c726774` |
| S | `ProofProject/OuterToeplitzData.lean` | `dcbe4175ec4594aa389c8ee9321328d655ab6901532a65dafebef9952cbec039` |
| S | `ProofProject/PeakClock.lean` | `e88676fea2b6f0e375e91180559188f40974c45f46309e60f536a16e3f73bb26` |
| S | `ProofProject/PhaseCoefficientPolynomial.lean` | `717f9105e73b7b8931bba2143769d79d2b857cefe345f0955fcb93c1adff6201` |
| S | `ProofProject/PhaseDeficit.lean` | `61414f0d9a4b7faf0dfaac071fadc7559559dc447e420f580b6797bd4381b726` |
| S | `ProofProject/PhaseIntegralEnergy.lean` | `4dfb5989e3d4380f550ec05f4303927e797309c324e075a29d8427e8f787c48b` |
| S | `ProofProject/PhaseQuotientIntegral.lean` | `2d8157d4f9558f05cf86b65e5042124a24ad531a730542790e79a9c8a155f5a9` |
| S | `ProofProject/PolarFactorAlgebra.lean` | `1dc8a723037ddd5d3197ce7193700c4da542e99bb44ee2c32cb2e806f82f4f68` |
| R | `ProofProject/PolynomialGeometryReduction.lean` | `edcd9926988985d246e01b5ff412c1c198f7d16d9cf804087506de7a25195862` |
| S | `ProofProject/PolynomialLaurent.lean` | `b0d0c543e781a6f225d9bfe99f0c33cbe061ab98cc9dd5a6f7ca5aeda69c8fbd` |
| S | `ProofProject/PolynomialPhaseMoments.lean` | `17bee753b329d85fa661bba4af91189ca88298242618af28791da1796076864a` |
| S | `ProofProject/PolynomialRadialMaximum.lean` | `3da51c4fb94240fc25adf2234074ecc5625bb0a900f9c6acdecdace8fd3b27ef` |
| S | `ProofProject/PositiveCircleFactorization.lean` | `42b94841efa157094f38840b3f4651aeccd7f71dc725f56998ca9a0703e59b01` |
| S | `ProofProject/PowerAmplitude.lean` | `e2bc1a6abff3f6cc84524aee42615d46993d79e7615248c23da83234606911b8` |
| S | `ProofProject/PowerIntegralBounds.lean` | `e20e40d017cfd56e2a6e516ec5c33820d4c081f6e7af394a5cf1100eb20b3efd` |
| R | `ProofProject/PowerTailIntegral.lean` | `81e92bb6cc05290895018f39a9c03800cf6270dc42e6924c02d96313544088f2` |
| P | `ProofProject/ProjectionAngle.lean` | `8aa1c7e8b981d9865d2ef9a226fca305dae4095fff9177893dbd2d1fbda9f27b` |
| S | `ProofProject/ProjectionHankel.lean` | `dbb43d785ef58a6f6b55c06536bbd5e5f8016329270df8aa491d476f1643bea7` |
| S | `ProofProject/RationalCircleAngle.lean` | `57d22d5ae3a3622ff436025ec099908bcddd7544906d6d58f1e5661148369c85` |
| S | `ProofProject/RationalPhaseApproximation.lean` | `ae22c0478e9227317f1745594a65e442b9313d58e6af88a8c95a233b9fbdf259` |
| S | `ProofProject/ReciprocalPolynomialApproximation.lean` | `8dc73606731e4b7415a352cd2d5361e9a6cca5b82c108b4ca447366c01401b8e` |
| S | `ProofProject/ReciprocalSqrtSeparation.lean` | `6cfe4734ce8324dcf0cc7c044e05db2ea475cdba94df50fac437ff2349cfbbbb` |
| S | `ProofProject/ReplicatedSpace.lean` | `d5d169fdfab7e70f3f64d08eadaef5b210dd91d25484f5497aacef11b70d7b94` |
| S | `ProofProject/ReplicationBound.lean` | `68e8169eb89f0b5efbc9f9978b5c1fd89d25caf838ba8270135f2a90face660e` |
| S | `ProofProject/ReplicationDeficit.lean` | `2f970a11c52d284d23380232fceed2389de3e382e8ac3887a195dc303b73ff70` |
| S | `ProofProject/ReplicationEnergy.lean` | `997c42e66c7feb23c1e2538c34371f8796b441051e0e55f021066ad41c3412ce` |
| S | `ProofProject/ReplicationLower.lean` | `a5b6299fb255272e79391d0ec11fb901ca0905918a4d69fde60265583e1422c1` |
| S | `ProofProject/ReplicationModels.lean` | `c177b853218bccc791c3a0e38d295e6b05df360b08730a85e8933f071bb26fe7` |
| S | `ProofProject/ReplicationOrder.lean` | `b088c02c42b2387d7eb433d4a3dccf33a7f41c557b2ca17b00b7194142075e0e` |
| R | `ProofProject/RescaledResolventInverse.lean` | `95e86751c640b3a7be0102421e78f9c92819e4a67e6d9e1cef7a3f8646c5f885` |
| S | `ProofProject/Rescaling.lean` | `dc0f13c557d7e5390db9de9e7edd375f48ddff91e2494ed885d804d4ecc03776` |
| R | `ProofProject/ResolventAverage.lean` | `dc3f41693058d35ad40646b39afad9862cac24a7168c3f3ea9122692833eb516` |
| S | `ProofProject/ResolventConvolution.lean` | `0e406e49535873a474e5557eed98898857661e9bfc31b7a6fa93d5bbd7ea67f3` |
| S | `ProofProject/ResolventKernelIntegration.lean` | `8a8971c20cbfd556f536f77f0570916f41de4cd8c0733357739a558e15c81b92` |
| S | `ProofProject/ResolventOperatorIdentity.lean` | `5d03246a16cd24896ccc420552474f1334b4a34aa4ae7d9b49d91c936026a647` |
| S | `ProofProject/RoundedOperators.lean` | `b6052964a9b55b10bceaf7e96dbc9ef299c89cce8fb7cbfb1085d4036aea7e9a` |
| S | `ProofProject/RoundedSemigroupBound.lean` | `95832d1434ed79b0785db1edac08b7162dde975b471322312694abec73f8be07` |
| S | `ProofProject/RoundedSpace.lean` | `dd81e1c2012e21e188b8a485858901745e8580a60926d9e978f5ad711897d46a` |
| S | `ProofProject/ScalarEigenvalues.lean` | `d6f86e013ffe23def71266830d9c319744d15f7eb598783cc683790c63051add` |
| R | `ProofProject/ScalarExamples.lean` | `7728f68bb1cacb3268aa3155218adab91274758d4d1988681fd410fae6519e60` |
| S | `ProofProject/ScalarFourierReconstruction.lean` | `e63d5a814b49de9497559781b738f268c2b5bff8b7c6d61d0c43b5859f2dc599` |
| S | `ProofProject/ScalarSeparation.lean` | `d4a5169bcfef58fd94dd1bb8b5a1185e5ae8495b1f8f8c171842bc15f771b771` |
| P | `ProofProject/SchurContraction.lean` | `9790e35039a1fedac9d018cd6442c6598064590aa8807bc7e60145a46088030b` |
| S | `ProofProject/SchurData.lean` | `25534983e9a295234732a1472f1bbc543d2da483f76ae00dd5a2bb9ab16e14c4` |
| S | `ProofProject/SchurFraction.lean` | `deb096d275e2a59550536d4ac56b9378643bff9a27dbdb080d9a4274b53e40ba` |
| S | `ProofProject/SectorPower.lean` | `53226a82b58be5184cb4e28ac3b27504253995f1b399213655f935cc37746c33` |
| R | `ProofProject/SemigroupKernelConvolution.lean` | `5480b8a1d165f9221b989bc0d63aa6c8b15994f41ced18cb1192a3a2107ed67f` |
| R | `ProofProject/SemigroupKernelOperator.lean` | `6017a38b10a257a7d6832c7e333eb4f567f93cdb68a6e0f9692bf56b1fbdce66` |
| R | `ProofProject/SemigroupKernelSeries.lean` | `5aa60a8c82dacf1ffe178685863c0409386e63d5092a1dfccd755b3aa71a1b8b` |
| R | `ProofProject/SeparatedFactorSum.lean` | `e70b83979768e77a3aa990fd99cc252960a3e7f3f17a95f37958d96998ff3759` |
| S | `ProofProject/SeparatedIntegers.lean` | `b4650fd347f2e29ea99fc5eba5a62ade4d150057b974e77df5aa8b94fc93ca77` |
| R | `ProofProject/SeparatedOperatorSum.lean` | `3decd6c1a0a0c80db0095f8b26b6f6fdd22b5c972242218a715e73135125d391` |
| S | `ProofProject/SeparationScale.lean` | `67821cd02afa5763b631b078de9264fc94e726510f02632e3b1fe0b7b381ead7` |
| R | `ProofProject/SeparatorBudget.lean` | `20b762771677ce222d1126fafb7ee2663fa6228f26164edbde99e304008d18ce` |
| R | `ProofProject/SharpGrowth.lean` | `2e592957ed0f13c37c430adaf7e775efa181ed955dcd17f01458ac3771b7a877` |
| R | `ProofProject/SharpTailGeometry.lean` | `3acce2b347430f625c3cb36633036c67f6a04340162db0b280baf1afde252a6c` |
| R | `ProofProject/SharpUpperBound.lean` | `fc208f2160dec4df29c6430a0d26a7a1387ad5a9de87a90c1e4b73050ae5ab31` |
| S | `ProofProject/SignedTransformedAmplitude.lean` | `7e0f18894baae96cf72af2265a17287a1f724b98f136c64745eaafdf582240fd` |
| S | `ProofProject/SourceAmplitudeConjugation.lean` | `be017db0476581f947bf8c3bbda3bc35faa4b9eebceecad7d644797aed3d8266` |
| R | `ProofProject/SourceBesselRemainder.lean` | `3a93ec1823a23deca123d0d342b0ca72b3fd20396bf6956d3a0434fb5c63122b` |
| S | `ProofProject/SourceBoundaryEstimate.lean` | `a009d41818421ab36b8e5d72796aa815f0868e4898133de87b2f5701d3ebf6b9` |
| S | `ProofProject/SourceBoundaryLower.lean` | `32b4ac28b9d2cd1a3f4bade1fa13d768159c88b37edc51fbac02289f0b125fe1` |
| S | `ProofProject/SourceBoundaryMoments.lean` | `db5d84bec586040f638c22f003f2727693a1c911320d7a25e94e01d196eb2fda` |
| S | `ProofProject/SourceDirichletGain.lean` | `d4a8e30dc1881688a5dbfa581a43826a1b987d924e5d6f9fa177455bbe70909e` |
| S | `ProofProject/SourceFrequencyNormalization.lean` | `397783b20e2d00a2435165345dab793f47103bf68702d21b2d7f98c5019648dc` |
| S | `ProofProject/SourceMarginIntegrability.lean` | `2049f7f2e85d73d84548d79a53a50fe4e758e3ab455fd489a7b8dc6d618a3372` |
| S | `ProofProject/SourceMomentConvergence.lean` | `1229a1ed8d20353b06e835844a573d7847f807fc6a2c4b644bb7de02d9b73996` |
| S | `ProofProject/SourceMomentDefs.lean` | `0e3f98d5796fa09f4a959456e5d775f0ecc6be91280b96a8f727b30bcca4515d` |
| R | `ProofProject/SourceOscillatoryOperator.lean` | `904306c5a5f895e445c56b5be46287a1f128dfe84db41c4d2ec2827ef1ceb24a` |
| S | `ProofProject/SourceOscillatoryPhase.lean` | `8e30ef610f6e037b629ccb43be77a1c4cefec7760a6c2230d5b1dd5277cac968` |
| S | `ProofProject/SourcePhaseCorrection.lean` | `7761aee9c5e77d95357d045f2159a62d36fca8c23856cfda23ad2d7216af8986` |
| S | `ProofProject/SourcePhaseDefs.lean` | `918b25fe0973e5a625ddf46441d5a29e9ff8f8eaa379ee0f13aa2508195af6aa` |
| S | `ProofProject/SourcePhaseMargin.lean` | `9c01f1bb1c8ef27e8fc1587817191f1d2f376df1680ad1a64f0adb0930669f76` |
| S | `ProofProject/SourcePhaseMeasure.lean` | `fca31f1654be961bf39b3d7c3b88572868d3ca12e6a7568618dadb5179e20808` |
| S | `ProofProject/SourcePhasePolar.lean` | `0df5c9be653406b9a261782120128ffd62a2d59781fda28394d5270593ca9375` |
| R | `ProofProject/SourcePieceAmplitude.lean` | `62209e6df67a69714287bce5fe4b2c98cfbfc77bc048b8891bdf3f03522eb256` |
| R | `ProofProject/SourcePieceClock.lean` | `25526c841c96ca22c7a64d81262919ef95537650fac35f86eedf26cbe89cbdba` |
| S | `ProofProject/SourcePieceCutoff.lean` | `4da70d90e27239c951acd714ba49325ca9bcd0e9691b8b73d527bd50ad359129` |
| R | `ProofProject/SourcePieceDampedTail.lean` | `0b3203bd2c783892b177d22219d007f2db078cd74902729d856c6c3d1d67df00` |
| R | `ProofProject/SourcePieceError.lean` | `e81b4e6ac1fc11b85c6b3f190d14799fc059ddab46d4cfb76f917f33d10a2c86` |
| R | `ProofProject/SourcePieceFiniteSum.lean` | `f053e54ad88623035195e6c21ae96e53e5f5b68495a4d3c3bb90c9f89e7b4594` |
| R | `ProofProject/SourcePieceLimit.lean` | `953a75cd3b08bfb6b7b722ae0c7f2d482d14cfaeb81b5f402becbc31a3c3de0b` |
| R | `ProofProject/SourcePieceOperator.lean` | `75368d41bc409c0ee68f13f415cebb7af0456ea8c2e63832facd5a9a6c117d4f` |
| R | `ProofProject/SourcePieceResolvent.lean` | `a18312a430f263772a7cd953fdcc090db5eecc24d57cef643c466328ae053ec6` |
| S | `ProofProject/SourcePieceScale.lean` | `77e8eb60fac679efd976b3488e4b4a17130ce4084573656f22ac377382c8e012` |
| R | `ProofProject/SourcePieceSeparation.lean` | `b68e19a550ce07dc5a0f554f1d964132c8dca37ae5b3dfe9d0e315b3a6d92df8` |
| R | `ProofProject/SourcePieceSynthesis.lean` | `576d758acdc20aa5cac0676620cc2c2b70d95c3b0673ed36c02461abddb75a27` |
| R | `ProofProject/SourcePieceTimeBound.lean` | `f02eb76ccc3328563480161ec88e6068bcca383b29834cc3359e5adbc7237405` |
| S | `ProofProject/SourcePolynomialGain.lean` | `c3aea8a5adfaf40929f8b01854456d99c41b1b568a7c6d5cee8f64d66e5f170b` |
| S | `ProofProject/SourcePolynomialHilbert.lean` | `87e1a530a2bb8e36999b6d48491bf8c4d1c4473edf8cbbd2b45925c6d2e8117c` |
| S | `ProofProject/SourcePolynomialInner.lean` | `7cc477a742b9c4f226a1c20d1120c5aa11b961e38fe3c2ed75b37859aedf73ad` |
| S | `ProofProject/SourceRadialBounds.lean` | `f6f63d53e4dbecdb8720b843b24a64c75ec305e2886dd44feedd8a95ef3306aa` |
| S | `ProofProject/SourceRadialIntegrability.lean` | `19bea9cd4f231d45fd495789940bee8f18a1e3da61324246355e9517e26d11d8` |
| S | `ProofProject/SourceRadialLimits.lean` | `405efb96b5d39f5b518b5ea811e368b3a622c30b80d474e10f76dde15b872f53` |
| R | `ProofProject/SourceScalarBudget.lean` | `d8348e22ce513e287fd33fac1f03aabbbf6f7ba551a6863bd05efceb371511d0` |
| S | `ProofProject/SourceSeparatorScale.lean` | `666c05fccbfcdf8d5003e55d108e00af7bd7c553f0b9c62dd6e055caf0cd75e4` |
| S | `ProofProject/SourceWeightBounds.lean` | `167cc6fc6c943bc7fe34cbfc5e6046b90fbf337167c75283642faf753e53942a` |
| S | `ProofProject/SourceWeightedAmplitude.lean` | `6d16252e2264b77670fa848ed977ac0f62be117cdaf46270035009ba66ff3c60` |
| S | `ProofProject/SourceWeightFactor.lean` | `a26e3f9c749aea37e854023183cea8b6ed7be1e732670b77e5e606c91479be92` |
| S | `ProofProject/SourceWeightParameters.lean` | `aa985193ae638ce42ccece3d9259c144d7216a609241193167129817567200b7` |
| S | `ProofProject/SourceWindowAmplitude.lean` | `905803a7820f65712c676195402d2d4dbaf36995fccd84d3eb73b226407174c8` |
| S | `ProofProject/SourceWindowDecay.lean` | `957095ce840196d5f3cb01014959bb7dfed7c2bc291d48ec1f3796da7220d43a` |
| S | `ProofProject/SourceWindowPhaseBounds.lean` | `fae3f56653abf8a7e4208594c7ee4de37e586ab587f4fd62badf1777d1ce1a44` |
| S | `ProofProject/SourceWindowPointwise.lean` | `00856e830886c0d296a2e919fde56bed7e284e474fa1681a4b5bd4959b30ec82` |
| S | `ProofProject/SourceWindowRescaling.lean` | `47fc1090bd2e9c59b05258a025b8a1e7cfc0d81da2c18b71a61c5b602f396b68` |
| S | `ProofProject/SourceWindowSmoothedDecay.lean` | `06eb3ed316309605683cde61e4928a37f0c54ba7139cc8ad628bd800e1048f68` |
| S | `ProofProject/SourceWindowStationary.lean` | `95e0923832eee8c4cd13fd84391a1e03aab2929b7860f2f6d662a4b1864eec46` |
| S | `ProofProject/SourceWindowSupportScale.lean` | `54fa1f0153afaa313f0d370e45bc608b469fe913da95eeb774b664cef809851e` |
| S | `ProofProject/TailBoundaryAlgebra.lean` | `af3283cb3f356b4aeea8aca88602c8804e206ef42c83ab48e54f2453d7996d00` |
| R | `ProofProject/TailGeometry.lean` | `7844de0f0b496ff4d0e2999b819687d4f7b30a13c9d12881737e842928662eff` |
| S | `ProofProject/ToeplitzBoundary.lean` | `7fd670d4431476b068f137749586f9480c607b23c416052c0177bf1ef01e1853` |
| S | `ProofProject/ToeplitzPadding.lean` | `02a39cf640f3efca2af315bf099e857d3201a70a681f83c4350d432d1913fb51` |
| S | `ProofProject/ToeplitzPolynomial.lean` | `52f6688b423e8055a006b5adcf9b69f3e382e390e43a7b82306dde2ddfbee5c2` |
| S | `ProofProject/TransformedAmplitudeBounds.lean` | `3c52c387f00faf54db383978287f0ffc218a98c7b488ee3ba8ea5e8698b05087` |
| S | `ProofProject/TrianglePartition.lean` | `e8b03211c579f125e8614cac71857660ae214072d1eacbbf06ca1c4947f3a322` |
| S | `ProofProject/WeightedBoundaryEstimate.lean` | `0e5e2f79ddae216e2f86e9661f3e748d9fe14eae20af2f57538d6e6454226123` |
| S | `ProofProject/WeightedCauchySchwarz.lean` | `8d483c282ee0dff3c0da7bac3d857a2b174484121a033885b09e265cf037b476` |
| S | `ProofProject/WeightedCircleProjection.lean` | `407102439c793d3c8f15cd0ded1aef02574da2fb1846a5d36e439dd67d020a51` |
| S | `ProofProject/WeightedDirichletBounds.lean` | `d608629814ec531646242c1037a5bd336cf056626ad657c46cff2fedc485c26a` |
| S | `ProofProject/WeightedPolynomialAngle.lean` | `8c760d14bf0d76e6090447ac9dda9d229f6a14420fffccbe70bba8839182c3ab` |
| R | `Solution.lean` | `cea58f6ca9fa54d0a8951e356f38d42f51e95ff6bdb101039e94303c91d7567c` |

P excerpt line intervals: `ProofProject/AveragedFourierOperator.lean:30–54`; `ProofProject/CircleGramPolynomial.lean:35–60`; `ProofProject/FiniteHankelForm.lean:79–106`; `ProofProject/OperatorPolarRange.lean:42–85`; `ProofProject/ProjectionAngle.lean:9–42`; `ProofProject/SchurContraction.lean:36–65`.

All of these statement/configuration/protocol documents were read in full:

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `b8a14a878b4a8aced61b0de4f8f5d90b2c488e9d5c63a7748a9a84092982b4d6` |
| `NUMERICAL_TARGETS.md` | `8f02633f51ae3516e23ace8000310532bc28909d853c99a9d024a6e32367c901` |
| `lakefile.toml` | `95458a5f2e532fd06d67e5c774020f7d017036b4470c4a45d7cbca203464901d` |
| `lake-manifest.json` | `0acce5272fbb94ad70c33f39f1d7832bd17fa7e6fefb3b5076514d38e9b14502` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `/Users/april/Documents/overleaf/MF-17/OpenProblemsInNLA/matrix-functions-and-stability/MF-17/README.md` | `5c7f922fe777090b92c593447142ea4135a6be54914f11cf081397c017ae640f` |
| `/Users/april/Documents/overleaf/MF-17/OpenProblemsInNLA/docs/lean/REVIEW.md` | `d967ddce620d4e754e2f9c25548f30cb537f76f4ddcf8ecf2574945bcd332553` |

Pinned Mathlib excerpts only; hashes identify the whole containing files, not whole-file review. Paths are relative to `.lake/packages/mathlib/Mathlib/`.

| File | Inspected lines | SHA-256 |
| --- | --- | --- |
| `MeasureTheory/Integral/Bochner/Basic.lean` | 182–210 | `f81a06eab17faccbc4b671a93e7af73332f5fd3946f7690e7c2a3cfee77d28c8` |
| `MeasureTheory/Integral/DominatedConvergence.lean` | 85–114 | `18b709ea5c9ef9136e3e75ded82a6135641e6e19688e0ca3abcb0af45648ab84` |
| `Order/ConditionallyCompleteLattice/Basic.lean` | 187–205 | `4e4c9abe9993f2334c389d6cb4b75b31b44bb66bb87b65a95b3abac2dbd9fcc8` |
| `MeasureTheory/Integral/IntegralEqImproper.lean` | 685–722 (limit theorem statement and beginning of proof only) | `9b23ece88109c97647472e92ac73478da988c81436efc63e17a2acfb2db15353` |
| `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean` | 1103–1145 | `5fd64054d9ae8bfce585ff809933a756bcf2d224ef144ae24c8fe8870c68050c` |
