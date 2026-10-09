# TR-07 independent proof-core audit 1

Reviewer: OpenAI Codex AI agent `/root/choose_algebra`.
Independence: I did not author or edit any TR-07 definition or proof. My writes are review reports and verification scripts/logs only.
Phase: interim mathematical audit while final assembly is unfinished.
Finding: **No mathematical blocker in the reviewed core. This is not final approval of TR-07.**

The worktree HEAD was `1b27d9f89eb41d1b7a2adfdfb33d870a8d6f31a5`; the proof modules below were uncommitted. The source problem and protocol are the ones identified in `statement-1.md`. I rechecked the frozen Definitions and Challenge hashes, which remain `d80638b68ed9fc06f3013edfefb743965de664c4bab312d03e239ee25fc80233` and `0371225eaf7dfcf5691590cfcdd8bacbece0ceddb8716b04c01cd365ee3202cc`.

## Scope and actual file hashes

I read the full source of these nine requested core modules, plus the three local probability/vector/path dependencies that determine their semantics. Paths in the table are relative to `NLA/TR07/`.

| File | SHA256 |
| --- | --- |
| `ColumnAction.lean` | `fac1c1d421e5baa9141d32585360c170226e48ea5a69f676410adb6f9a38b592` |
| `DeletionDefect.lean` | `c38411cabfb62876e1fc391ef2b2f551bb9f74825ab63b0700cdece98f5d4228` |
| `Witnesses.lean` | `519ac07ff4add8b90bfc9bdb8c0b5c04b456807a8ce4352b3dd18c86e886d18e` |
| `SpectralFilter.lean` | `82611c1c7ceff64d014d63e53e48c3b0adcd2a6a7616771f29b946e706ee9a94` |
| `Covariance.lean` | `8e56453141421c8d80160b2c9fa4ca3c83f6c3819c38935d76f20b89ae5c8387` |
| `SignedVectors.lean` | `f7c91dea4e043d195cb0d172f7c1222295a0d9f447fa1ba007b2fa33adb44b0b` |
| `CovarianceFilter.lean` | `311f1e4d6046f3e1f8069846b9540d187d89026e0bfc56c686b57e0c14145f05` |
| `FirstHit.lean` | `aaca7b4415d63239392d37cd7ef80e95b85d1c1cd0a2f4d7a51354cba5236bb5` |
| `CoupledPaths.lean` | `5febc86960cce6b910ed93374a72a65f2023d81405c2dd0d29a6e6a79e04fd86` |
| `FiniteProbability.lean` | `b9406c005ef1371e106d3731532c95c168424f892ae01af8875524c8994b779d` |
| `FiniteVector.lean` | `01cdf1463172648cc84e414df6e37ce38542dd69ae4339172b07e045a4d221ba` |
| `FinitePaths.lean` | `0ff9cafa1ca86d4a9e0383a70bb4db214aa7d56c5706e09652ecb8ed2a6cbfc4` |

## Mathematical audit

`ColumnAction` uses a genuine finite linear synthesis map with Euclidean coefficient norm. Its `Good` predicate quantifies over every vector supported in the indicated set. Empty support is proved good through the zero vector, so deletion existence does not assume invertibility. `selected_unit_le` supplies a concrete norm value as an infimum-set member and supplies zero as a lower bound before applying `csInf_le`. `good_selected_of_tail` normalizes an arbitrary nonzero vector and treats zero separately. No unit-sphere nonemptiness premise is smuggled in; an actual normalized vector supplies the needed member whenever used. This correctly proves the one-way bridge required by the strict tail event.

`DeletionDefect` is the least deletion cardinality found by `Nat.find` from a proved nonempty set of possibilities. `exists_optimal_deletion` exposes the witness, and `defect_le_card` exposes minimality. Its replacement inequality adds the exceptional positions to an optimal deletion set and uses restriction monotonicity; both directions give the absolute bound. Reindexing is an isometry and cardinality-preserving transport, not an assumption about the statistic. These arguments work for repeated columns and arbitrary labels.

`Witnesses.defect_ge_half_of_witnesses` proves the desired lower bound from an expansive witness map and the actual total squared synthesis errors. The kernel of deleted-coordinate restriction has dimension at least the number of witnesses minus the deletion count. An orthonormal basis of that kernel gives surviving coefficient vectors. The lower bound in `Good` applies to each such vector; Bessel's inequality bounds their total image energy by the full column energy of the witness map. The resulting stronger three-quarter lower bound implies the stated half bound. The argument never assumes orthogonality of errors, disjoint reservoir usage by different witnesses, or bounded reconstruction coefficients. Positivity of `eta` is explicit where cancellation by its square is needed.

`SpectralFilter` proves its scalar inequality by a geometric sum for all natural exponents, including zero. PSD eigenvalues and the upper quadratic-form cap are used to put each eigenvalue in `[0,s]`; unitary diagonalization transfers the scalar bound back to matrices. `Covariance` is literally a finite weighted sum of outer products. Its PSD, trace, quadratic and transformed-covariance identities follow from that definition. `weighted_trace_le` correctly requires only a nonnegative diagonal weight and obtains diagonal bounds from a PSD difference; no commutation of the covariance with the diagonal is assumed.

`SignedVectors` makes the exact signed-entry and support-cardinality assumptions explicit, derives squared norm `s`, and proves the sparse quadratic-form bound by finite Cauchy–Schwarz. Incidence is the mean coordinate square and therefore the incidence probability for signed entries. The regularized diagonal has entries `p_i + 1/k`, is strictly positive when `k > 0`, and has trace `s+1`. Zero incidences are retained rather than inverted. Adding its positive diagonal correction proves the covariance cap.

`CovarianceFilter` handles the nonsymmetric transition matrix through the diagonal square-root matrices `S` and `N`, whose inverse identities are proved from strict positivity. It explicitly establishes `P*S = S*Q`, transports powers, and computes the covariance trace as `trace(D*R*Q^(2L))`, using the proved commutation of `R` with its polynomial `Q`. The only spectral contraction bound is for the symmetric conjugate `R`; no Euclidean contraction of the original nonsymmetric filter is asserted. The bound `2*s^2/(2*L+1)` follows using positive natural sparsity. Singular covariance matrices are allowed throughout.

The local `Law` structure consists of nonnegative real weights with a proof that their finite sum is one. Expectation, probability, product, iid law, map, and bind are literal finite sums and products, not abstract assumptions. Markov and Chebyshev are proved from pointwise finite-sum inequalities. `FiniteVector` proves the exact mean/variance decomposition coordinatewise. `FinitePaths` records exactly the post-transition states and derives the `(j+1)`st mean iterate from the one-step mean identity.

`FirstHit` recursively returns the first acceptable member of the actual chunk, or `none`; its support theorem proves that a returned sample occurs in that chunk. The first-hit expectation and individual weights are derived by induction on iid tuple length. The geometric bound includes zero incidence and zero chunk length, and invokes positive dimension and `ell <= k` explicitly. There is no conditional-on-all-hits law asserted.

`CoupledPaths` retains both every independent input and every resulting state. It proves the iid input marginal, the Markov state marginal, pointwise support preservation, and scaled expectation domination by induction on path length. The domination proof uses nonnegative test functions and nonnegative scale before multiplying or iterating inequalities. Thus path-dependent transition success probabilities are handled without incorrectly identifying a conditioned law with the ideal law.

## Reuse and quality

I searched the pinned Mathlib for related normalization, orthonormal-energy, finite probability, and first-hit machinery. The substantial linear-algebra proofs already reuse Mathlib's Bessel inequality, rank-nullity, Hermitian spectral theorem, PSD congruence, geometric-sum identity, and finite Cauchy–Schwarz. The short wrappers connect those APIs to the problem's actual objects. The finite real-weight `Law` overlaps with Mathlib's `PMF` constructions, but its normalization, operations and estimates are fully proved and its intended final semantics are a real finite-cardinality ratio. I requested a short documentation explanation of this deliberate representation choice; a separate PMF equivalence is not required if the final bridge to the frozen ratio is proved directly.

One optional simplification was reported: `ColumnAction.norm_normalize` has exactly the conclusion of imported `norm_smul_inv_norm`, so that wrapper can reuse it directly. This is not a mathematical defect. The build also reports unused-variable/unused-simp lints and one deprecated `Matrix.ofLp_toEuclideanLin_apply` use in `Covariance`; none is a trust or scope failure. They should not be mistaken for a clean warning-free build.

## Independent mechanical evidence and limitations

I independently ran a local `lake build` of all nine requested modules with Lean 4.33.1 and pinned Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. It succeeded with 3212 jobs and the lints described above. I also ran a reviewer-owned file containing imports and `#print axioms` commands for fourteen principal core declarations. Every printed list contained only `propext`, `Classical.choice`, and `Quot.sound`; none contained `sorryAx`, a custom axiom or a native-evaluation axiom.

| Evidence file | SHA256 |
| --- | --- |
| `verification/CoreReferee1.lean` | `01212145eb1e64e5ac77a502c29afe7299c2bf19346f0e7b64d74376fe699b37` |
| `verification/core-referee-1-build.log` | `92eeb856216eecc5844087560202a37ef5402ed31f7eb32ddb10bf3f8d599ac5` |
| `verification/core-referee-1-axioms.log` | `44a674d80a1aebf213550c7f1251ac8ddc2bd001688a23ea779c62d9e426a2eb` |

These are cached local macOS checks, not fresh Linux verification or a Comparator result. This report does not approve the unfinished assembled theorem. Still required are independent review of all remaining proof modules, the actual ideal/reservoir reconstruction and common-reservoir witness assembly, iid concentration, collision repair, the equal-fiber uniform-subset bridge, all asymptotic deductions, final source hashes, transitive exported-theorem axiom checks, and the repository's mechanical verification gates. No human review or source-author endorsement is asserted.
