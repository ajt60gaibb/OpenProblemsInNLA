# TR-07 independent proof-core review 2

**Phase:** interim proof review, before final theorem assembly.  
**Reviewer:** OpenAI Codex AI agent `/root/environment`, an independent nonauthor of all reviewed mathematical definitions and proofs.  
**Verdict:** No substantive defect found in the reviewed core. **Full formalization approval remains pending.** This is AI review, not human peer review or source-author endorsement.

I read the eleven requested modules in full: finite probability, variance, collision sampling, uniform subsets, probability transfer, finite paths, ideal kernel, ideal estimator, ideal reconstruction, independent blocks, and common-reservoir witnesses. I also read their complete local mathematical dependency closure, including the covariance filter and deletion/witness machinery, rather than treating the imported statements as unexplained premises. The canonical target and complete informal source were previously read for [statement review 2](statement-2.md); their frozen definitions, Challenge, and numerical-target hashes remain unchanged.

## Findings

`Law` requires nonnegative real weights summing to one. Its expectations and event probabilities are actual finite weighted sums. Product and IID distributions multiply weights; bind composes normalized kernels. No measure-zero convention or external probability oracle is involved. The finite variance decomposition and coordinate-replacement induction prove the required variance bound `<= r`, and Markov/Chebyshev are proved from those sums.

`exists_collision_coupling` constructs a joint law, rather than merely assuming closeness of the two sampling experiments. Each recursive repair keeps a fresh uniform draw when it belongs to the unused index set and otherwise resamples uniformly from that set. The proof establishes both exact marginal expectation identities for every observable and the exact mean Hamming cost `r*(r-1)/(2*n)`. The fresh-set cardinality is checked, and its nonemptiness follows from the strict cardinality bound at each recursive step. Empty samples are covered by the base case.

`rangeFiberEquiv` identifies the fiber over a selected index set with its bijections from `Fin r`. Consequently every unordered subset has exactly `r!` ordered representatives. `ordered_range_expect` cancels this nonzero factor, and `ordered_range_prob` reaches the literal `powersetCard` count ratio. This includes repeated column values correctly, since the finite law samples indices. There is no replacement of the uniform subset law by a convenient distribution on column values.

`subset_prob_le_of_iid_expect` has exactly the helper assumptions it needs: a coordinate-Lipschitz statistic, its proved IID mean lower bound, and the implication from the desired event to statistic zero on distinct samples. The event is contained in the union of a centered deviation and a collision-cost event, both with threshold `rho*r/2`. Its final bound is `4/(rho^2*r) + (r-1)/(rho*n)`. The final theorem must still instantiate these premises with the actual deletion statistic and singular-value event; the helper itself does not discharge that assembly obligation.

The signed ideal state is an explicit `Option (Bool × alpha)`: `none` is absorbing zero, and the Boolean stores the sign. `coordinateChoice` uses support weights `v_i^2/s`; `coordinateDraw` assigns weight `p(a)*u(a)_i^2/D_i` to a sampled column and the remaining mass to zero. Positive regularization is proved. Orientation is checked for all signed entry cases, including zero-weight coordinates. The resulting mean is the concrete regularized covariance action; no sign symmetry is assumed.

`paths` records post-transition states, and `mean_paths_coordinate` correctly uses power `j+1`. The estimator coefficients are `(-1)^j * choose L (j+1)`, with the binomial identity proved for the actual linear operator. The norm bound uses the complete coefficient sum `2^L-1`. `idealExperiment` first samples its center and then takes IID trajectories conditional on that same center. Vector averaging is proved coordinatewise in Euclidean space, and the error estimate combines actual bias and variance. `exists_estimator_parameters` chooses positive natural lengths and counts depending only on sparsity and error, before any dimension or column law. The success probability is obtained from the proved error budget by Markov's inequality.

The covariance-filter dependency handles the nonsymmetric transition by explicit positive diagonal conjugation. It proves the PSD majorant from signed sparsity, the trace identity, the regularized trace `s+1`, and the scalar spectral bound. It never assumes that the nonsymmetric filter contracts the Euclidean norm. The only spectral decomposition used is Mathlib's Hermitian matrix spectral theorem.

`Reconstructible` is membership in the actual span of reservoir columns with the prescribed Euclidean error. `defect_ge_half_reconstructible` builds one dependence vector per good center, with an identity block on center coordinates. Center and reservoir positions are disjoint by the sum-type indexing; reservoirs may be shared by witnesses, and no coefficient bound or linear independence is assumed. Its dependency proves the deletion lower bound using rank-nullity and Bessel's inequality. `defect` is the minimum over all possible deleted coordinate sets, whose existence is established by deleting everything. The replacement bound and reindexing invariance are proved. `good_selected_of_tail` connects the original infimum to the actual synthesis lower bound by normalizing a nonzero vector; its use of `csInf_le` supplies both a lower bound and a concrete member of the infimum set.

There are no requested mathematical changes to this snapshot. Minor quality notes from the build are unused-instance/unused-simp lint warnings and one deprecated matrix-action lemma; none is a scope or soundness issue. The finite-weight API is small and proves its own elementary probability identities while reusing Mathlib finite sums, Euclidean spaces, linear algebra, and spectral decomposition.

## Independent mechanical evidence

I ran, on macOS with Lean 4.33.1 and the pinned Mathlib revision,

```text
lake build NLA.TR07.FiniteCommonReservoir NLA.TR07.IdealReconstruction NLA.TR07.FiniteBlocks NLA.TR07.ProbabilityTransfer
```

This completed successfully with 3221 jobs. The observed warnings were the lint/deprecation items described above; there was no placeholder-proof warning. A source scan of the local module tree found no `sorry`, `admit`, added axiom, `native_decide`, unsafe/foreign implementation, or Challenge import. This scan is supporting evidence, not a substitute for the axiom check.

I independently invoked Lean's `#print axioms` through `lake env lean --stdin` for all thirteen of:

```text
Law.variance_iid_le
exists_collision_coupling
card_range_fiber
ordered_range_prob
subset_prob_le_of_iid_expect
Law.mean_paths_coordinate
idealKernel_mean
trajectoryEstimator_mean
ideal_reconstruction_error
exists_estimator_parameters
ideal_success_probability
Law.expect_power_triple_fin
defect_ge_half_reconstructible
```

All names are under `NLA.TR07`. Every output was exactly `[propext, Classical.choice, Quot.sound]`, and Lean exited successfully. The tool outputs were inspected directly; this report does not claim a retained full-build log or an authoritative Linux run at this phase.

## Snapshot binding

These hashes bind the reviewed source, not later edits. All paths below are under `NLA/TR07/`.

| File | SHA256 |
| --- | --- |
| `FiniteProbability.lean` | `b9406c005ef1371e106d3731532c95c168424f892ae01af8875524c8994b779d` |
| `FiniteVariance.lean` | `9d65f4f2ed23cf89cf5c7668c5c621fc5b55a749127010c4bb9b950b6f4848e1` |
| `FiniteSampling.lean` | `2e5d5a4fd312be2717268377519ff8bb67228d32ff384953fff56b43501aea89` |
| `FiniteSubsets.lean` | `8ffa8c61241834a8873f75283b500387b41633be18f65d64c2230bd883702f0a` |
| `ProbabilityTransfer.lean` | `b787c27de48ba50e6477eb735427dad13a8d1bee7dd4bceed134ed096ad8ca43` |
| `FinitePaths.lean` | `0ff9cafa1ca86d4a9e0383a70bb4db214aa7d56c5706e09652ecb8ed2a6cbfc4` |
| `IdealKernel.lean` | `791a11005ee7b457f9a7128690ae64b43f2c60a0689fb2ade53e3287985d3c70` |
| `IdealEstimator.lean` | `6b01720b03c428f6ed18f6084dedc7ccc71b1789485f26d56aae1bdb942ca4f9` |
| `IdealReconstruction.lean` | `63d693a596b211d592891c60e429212b47173141807c9c5e7511266dff0e581b` |
| `FiniteBlocks.lean` | `01894d28729ccda3ec1caf86269c5145d89913b3c61165c7b2e7f223f1f95373` |
| `FiniteCommonReservoir.lean` | `809106dc62df2cd0868e31720c300504dd6c8fb333ee8bcc327d6c42b5de378f` |
| `FiniteVector.lean` | `01cdf1463172648cc84e414df6e37ce38542dd69ae4339172b07e045a4d221ba` |
| `FiniteVectorAverage.lean` | `2f9f5999c1b8b1916dae3d3956113590e69a6d23464ace3038ba4dd8eab83ddf` |
| `Reconstructible.lean` | `01e923e10dde54cca425ce344cfa2a756c44fdba16f5c6e7eb10e40dc4e578c3` |
| `ColumnAction.lean` | `fac1c1d421e5baa9141d32585360c170226e48ea5a69f676410adb6f9a38b592` |
| `DeletionDefect.lean` | `c38411cabfb62876e1fc391ef2b2f551bb9f74825ab63b0700cdece98f5d4228` |
| `Witnesses.lean` | `519ac07ff4add8b90bfc9bdb8c0b5c04b456807a8ce4352b3dd18c86e886d18e` |
| `SignedVectors.lean` | `f7c91dea4e043d195cb0d172f7c1222295a0d9f447fa1ba007b2fa33adb44b0b` |
| `CovarianceFilter.lean` | `311f1e4d6046f3e1f8069846b9540d187d89026e0bfc56c686b57e0c14145f05` |
| `SpectralFilter.lean` | `82611c1c7ceff64d014d63e53e48c3b0adcd2a6a7616771f29b946e706ee9a94` |
| `Covariance.lean` | `8e56453141421c8d80160b2c9fa4ca3c83f6c3819c38935d76f20b89ae5c8387` |

The unchanged statement hashes are `d80638b68ed9fc06f3013edfefb743965de664c4bab312d03e239ee25fc80233` for `Definitions.lean`, `0371225eaf7dfcf5691590cfcdd8bacbece0ceddb8716b04c01cd365ee3202cc` for `Challenge.lean`, and `4780404e41c13668ee57f7c4cff51a4bc9a09fbe1f7ea1f30b6fa936fd7c7a08` for `NUMERICAL_TARGETS.md`.

## Remaining gates

This report does not review or approve the reservoir domination/assembly modules, final finite theorem, asymptotic deductions, complete `Solution`, packaging/status changes, or Linux verification. Their existence and correctness must be checked before final approval. A complete target theorem with all bridge premises discharged, its actual axiom closure, a frozen source snapshot, and the authoritative fresh Linux Comparator/kernel evidence remain required.
