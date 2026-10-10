# FR-05 independent local proof audit

**Reviewer:** `/root/fr05_proof_audit`
**Date:** 2026-10-09
**Baseline:** `180fd01d` (`Add reviewed Lean statements for all solved gaps`)
**Verdict:** The existing `Solution.lean` gives a local, axiom-audited Lean proof of the exact FR-05 target and its stronger uniform inverse-dimension bound. This is a source-level proof review and local build, **not** an isolated Linux Comparator or LeanCert kernel certification.

## Mathematical and numerical target

The canonical problem asks, for each integer $d\ge 2$, about an independently sampled standard complex-Gaussian frame $A_d\in\mathbb C^{(4d-5)\times d}$, with each real and imaginary entry coordinate distributed as $N(0,1/2)$. Its event requires that **every** pair $x,y\in\mathbb C^d$ with equal componentwise measurement magnitudes differ by one global phase. The original target is $p_d\to0$; the cited solution asserts the stronger $p_d\le C/d$ for one absolute $C>0$ and all $d\ge2$.

`Definitions.lean` defines actual complex matrix rows and sums, equality of every row norm, and a universal predicate over both signals. Its global-phase witness is `Complex.exp (θ * Complex.I)` for a real `θ`. `Probability.lean` maps the standard Gaussian on every real matrix coordinate through the factor $1/\sqrt2$ and takes the event probability at exactly `4 * d - 5` rows. `Geometry/InjectivityMeasurable.lean` proves that the all-signals event is measurable. The two final exports in `Solution.lean` have no analytic assumptions: one states `∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d → phaseRetrievalProbability d ≤ C / d`; the other states `Filter.Tendsto phaseRetrievalProbability Filter.atTop (𝓝 0)`. Thus neither the source law, all-signals quantifier, $d=2$ endpoint, nor the asymptotic conclusion has been replaced by an easier target. The proof uses existential $C$, as does the cited theorem; it does not assert a source-unsupported fixed numerical value for the final constant.

## Proof dependency chain checked

1. `Proposition31.lean` proves the planted-frame injectivity probability is eventually at most $113/M^2$: a good sampled Newton event produces an exact noninjective pair; its complement has the stated probability bound. `Planted/PlantedHaarFailure.lean` transports this bound through an independent unitary orientation, preserving the same injectivity event.
2. `Likelihood/LikelihoodIntegration.lean` proves `proposition_3_2`, an eventual $L^2$ bound `sourceLikelihoodL2 M hM ≤ C / M` for the concrete planted and reference likelihoods, via the overlap-kernel estimates.
3. `Bridges/SourceHaarPlantedDensity.lean` identifies the oriented planted sampler with the planted likelihood relative to the **original** Gaussian frame law. `Bridges/SourceReferenceLawBridge.lean` identifies the reference likelihood and proves its injectivity-event mass equals `phaseRetrievalProbability M`.
4. `FinalAssembly.lean` applies event-local Cauchy–Schwarz to the two likelihoods, then uses the two propositions to obtain, eventually, $p_M\le a/M^2+\sqrt{b p_M/M}$. `Asymptotics.lean` turns this into an inverse-dimension estimate and absorbs the finite prefix using $p_M\le1$, yielding one $C>0$ for **all** $M\ge2$. `FinalAssembly.lean` then squeezes $p_M$ to zero. `Solution.lean` exports both results directly from these proved declarations.

This is an independent inspection of the public definitions, proposition statements, law bridges, final derivation, and trust closure. It does not claim a new line-by-line mathematical rederivation of every analytic estimate across the 112 local library modules or independent validation of Li's manuscript.

## Local Lean and trust evidence

From `frames-and-matrix-designs/FR-05/lean`, with the pinned Lean 4.33.1 binary on `PATH`, I ran `lake build Solution` (successful; 3344 jobs, mostly replayed) and `lake env lean Solution.lean` (successful direct elaboration). The latter printed transitive axioms for both final exports and the sampled-law, likelihood, proposition, comparison, and finite-dimensional supporting exports. Every printed list was exactly `propext`, `Classical.choice`, and `Quot.sound`; there was no `sorryAx` or custom axiom. A source scan found no `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe` token in `NLA/` or `Solution.lean`. `Challenge.lean` has four intentional `sorry` fixtures, but it is not imported by `Solution.lean` or its `NLA/` dependencies.

The existing `comparator.json` selects both final theorem names and permits only those three standard axioms. At this audit point, the FR-05 local project had not undergone an isolated Linux Comparator proof comparison or a LeanCert kernel-mode run. The shared statement-boundary CI does not by itself certify the FR-05 proof. Any new infrastructure work should record those runs separately; the local Lean check and transitive axiom audit alone do not establish them.

The historical `verification/library-cleanup/source-sha256.txt` manifest currently fails on **four non-Lean canonical files**. Its 112 local proof modules and other Lean source entries match. The mismatches are:

| File, relative to `lean/` | Recorded SHA-256 | Current SHA-256 |
| --- | --- | --- |
| `../README.md` | `afdfc41880e24266f70da13427d8efe3a5015f345fd916884ecfd3392d61f31a` | `fcf01b335bccd51d025c1184a4b668f52431af9209cf5d88dcb7e95345507554` |
| `../formalisation-plan.md` | `6b510ded9281ceb31fdb8146956f2ec03b04e11f6a3d7fcf5db4377a9ee0e642` | `9a6cc89faff37742b4422a5ac02630ba97a1f22233570e0c8b966555c4bfe576` |
| `../problem.tex` | `2c8f3288a49313c1d589b9ea1381f361b0d962db0b10c2112eaa47cac072ba33` | `9e903eeda8b3544e904f0370148d76ed695ae7c5cfa9deaf775bfe76e7c8ac78` |
| `../problem.pdf` | `41e59f49d17c98bfe6c63502dfa96fdf7840e99c8b5b12c99ccb20cda2aa094f` | `8cc48d5a1d39143d823d9703daae402ca4d4c194e219051e51ebec64e8f0ce82` |

This makes the historical provenance check stale for the current canonical files; it is not evidence that a Lean proof source failed to match. A fresh manifest or new certification evidence should bind the current originals without editing their mathematical target or permanent ID.

## SHA-256 review inputs

These hashes bind the proof and canonical files inspected for this review. Dependency/CI files were being updated concurrently for the requested certification and are deliberately outside this fixed source snapshot.

| Path from repository root | SHA-256 |
| --- | --- |
| `frames-and-matrix-designs/FR-05/README.md` | `fcf01b335bccd51d025c1184a4b668f52431af9209cf5d88dcb7e95345507554` |
| `frames-and-matrix-designs/FR-05/problem.tex` | `9e903eeda8b3544e904f0370148d76ed695ae7c5cfa9deaf775bfe76e7c8ac78` |
| `frames-and-matrix-designs/FR-05/lean/NUMERICAL_TARGETS.md` | `c8a869a17f5eb85621a78a9de14ffc23a55c0d8ca183230311b17b877532f2c4` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/Definitions.lean` | `aaf435d209909c7d08114dcc2cfda9595408c5aa5a85537b0972032c0357a78e` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/Probability.lean` | `0aacb415bf3e8dd33359f6e8f25f52ea950c9b3e7014227f051c8bc11ee093c5` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/Geometry/InjectivityMeasurable.lean` | `417cb019d234d86f40e43594691e5d897333b75ae886b3e5089620b9619618bc` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/Proposition31.lean` | `9e6b557fc619f354c30aea2e11ec2ed6d0b4e3f08239f598471e2249b01fa124` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/Planted/PlantedHaarFailure.lean` | `ea939cff30a6ba4973ac3b2244bf114b502e6a39d302c7bac8aa5c896b7d2f01` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/Likelihood/LikelihoodIntegration.lean` | `3e7a5fa16aa579865c5eab7b01be8edc0563f9d9fe3fe8e1962d177c194d7f83` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/Bridges/SourceHaarPlantedDensity.lean` | `3b8acb366d2d9d20ccb3e379d42699dc06339534574014b8487bc2ba94b5fb35` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/Bridges/SourceReferenceLawBridge.lean` | `6f16dda41a0957f01b864581b0fa3ce829d14cafacb21aecbc3ec78c0e96f3d5` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/Asymptotics.lean` | `611945981b1351e8590088874ce98f232511b6d68665971746cba0ee2c27189c` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/FinalAssembly.lean` | `008ba33847b270562362eee8f0a58829837254e2e8ab02e5c66df69a7b835da8` |
| `frames-and-matrix-designs/FR-05/lean/NLA/FR05/Proof.lean` | `d862651b8a008ac4b938e5b1272d3320ba9e640f160d41f3ea4d372622e7a7dc` |
| `frames-and-matrix-designs/FR-05/lean/Solution.lean` | `7bdf86cd414a560f9bb470ef0bda254c1b7a4517922f00032d0ca9e78c7feec4` |
| `frames-and-matrix-designs/FR-05/lean/Challenge.lean` | `f92211491c88a6661f06f2ee64f596722f0f473481a915e1a429285bb927c776` |
| `frames-and-matrix-designs/FR-05/lean/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `frames-and-matrix-designs/FR-05/lean/comparator.json` | `166b5aa77ed2fdbaa9c47a662c7d048ba464a27a935b6679d87e8c0a000e7d14` |
| `frames-and-matrix-designs/FR-05/lean/verification/library-cleanup/source-sha256.txt` | `bb8ad0ac23bb81cf44b1c6ba24449933f996d5884c2f34a732a1defa7fbd894f` |

No canonical problem file, problem ID, or Lean proof source was edited in this review.
