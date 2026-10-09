# TR-07 independent final review 1

Reviewer: OpenAI Codex AI agent `/root/choose_algebra`.
Independence: I authored no TR-07 definition, mathematical proof, or implementation module. I independently reviewed the complete sources and wrote only my review reports and verification files. This is AI-agent review, not human peer review or source-author endorsement.
Scope: mathematical correctness, full original-target fidelity, probability and norm semantics, proof quality, reuse/API design, the proof guide, attribution, and the local evidence identified below.
Verdict: **APPROVE the complete mathematical formalization and reviewed proof guide at the exact hashes below.** There are no unresolved mathematical or statement-fidelity findings.
Mechanical status: **fresh sandboxed Linux/Comparator verification is pending**. This approval and the local checks do not establish the repository's final “Lean verified” status. An evidence addendum is required after an actual receipt is available. Publication metadata, which arrived after the proof snapshot, is reviewed in the addendum below.

## Revision, reviewed files and frozen boundary

The canonical source base is `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. At review time worktree HEAD was `1b27d9f89eb41d1b7a2adfdfb33d870a8d6f31a5`; the full new proof was present as uncommitted source. I read the retained canonical problem and complete `solution.tex`, not only its Markdown pointer, and followed `docs/lean/REVIEW.md`. I read every one of the 30 `NLA/TR07/*.lean` files and `Solution.lean`. The local import closure of Solution is exactly those 31 files; Challenge is absent. There are no unreviewed local proof modules hidden behind imports.

The complete per-file hashes are recorded in my `verification/FINAL_REFEREE_1_SHA256.json` (39 entries, including all Lean sources, the guide, target record, license and project configuration), whose SHA256 is `eac175c88a42350f82e023890d177851b5c77fea7902da16e35ebf6a96860729`. I independently checked all 36 entries of the author's `verification/PROOF_SHA256.json`, SHA256 `a499fc82cdebbe416686d7ecda0f105b50bad7bde1b9ba5fbdae71815ee4832e`: every entry matches both the actual file and my snapshot. No reviewed file changed during my build or subsequent axiom audit. These exact manifests bind the complete reviewed source set, not merely selected theorem files.

| Key reviewed file | SHA256 |
| --- | --- |
| Canonical `../README.md` | `1f2b4c9bfd606f49d2c522483a7375cff104744e7a540db1613bb01f91a281d0` |
| Complete source `../solution.tex` | `207eb87c6b47d3a3a1a529c49b7c5a4dcaf099a942d60fdc1b9b5e3285aae7a0` |
| Source pointer `../solution.md` | `307e8b419a4eb453e789120d86e1344b2aecaf8a8ce759f87d9585a470496fee` |
| `NLA/TR07/Definitions.lean` | `d80638b68ed9fc06f3013edfefb743965de664c4bab312d03e239ee25fc80233` |
| `Challenge.lean` | `0371225eaf7dfcf5691590cfcdd8bacbece0ceddb8716b04c01cd365ee3202cc` |
| `Solution.lean` | `dce1d7cb60d93d9453dfc73344a66c208f2e454a3d48edaac3ad48581306dfb6` |
| `NUMERICAL_TARGETS.md` | `4780404e41c13668ee57f7c4cff51a4bc9a09fbe1f7ea1f30b6fa936fd7c7a08` |
| Formalization `README.md` | `c2a7b570f77413bd4aa2f05a0f1c9db2178ce8998e431e0af6514390db6f6a35` |
| `comparator.json` | `019d6a019798a06088b14ddf2a2a7dc0e64b90d03b7d4afbf3062f04da6825b7` |

The Definitions, Challenge and numerical-target hashes are unchanged from my approved statement review. This report supersedes the unfinished-proof limitation in `core-1.md` for this complete snapshot while preserving that earlier audit and its evidence. It does not retroactively describe earlier partial checks as full verification.

## Full original-target fidelity

`random_column_subsets : SolvesTR07` proves all quantifiers of the original asymptotic target: every fixed `s >= 2`, finite `C >= 1`, sample and column-count sequences with the required aspect-ratio limits, every deterministic real signed sparse matrix sequence, and every fixed positive threshold. Sparsity means precisely entries in `{-1,0,1}` with exactly `s` nonzeros per column. Supports may intersect arbitrarily, signs may vary arbitrarily, and columns may repeat. No reconstruction hypothesis, dimension cutoff on the exported theorem, structural graph condition, or favorable random event is an input premise.

Sparsity is required eventually, which is stronger in scope than the canonical all-index assumption and permits irrelevant early dimensions smaller than `s`. The explicit `r <= n` is the domain condition already implicit in sampling an `r`-element subset. No inconsistent global positive sample-size assumption is imposed at row index zero. `aspect_ratio_bounds` actually derives eventual positivity and `r -> infinity` from the finite positive limit of `k/r`; the proof does not exploit division by zero at early indices. Nonvacuous families, such as `C=1`, `r k=k`, `n k=k^2` with repeated fixed-sparsity columns for sufficiently large `k`, are included.

`selectedAction` is the literal selected matrix product with Euclidean input and output norms. `smallestSingular` takes the real infimum over every unit coefficient vector, including directions in any kernel. The proof's use of `csInf_le` supplies boundedness below by zero and an actual unit-vector witness. Normalization handles every nonzero coefficient vector, while zero is handled separately. The empty-unit-sphere convention at sample size zero therefore cannot supply an eventual conclusion. The tail is exactly the required strict event `eta < smallestSingular`.

`subsetTail` is the number of good index subsets divided by the number of all index subsets of size `r`, using `powersetCard`. It samples indices, so equal-valued columns retain their correct multiplicities. The denominator is positive under `r <= n`. The final proof connects to this exact ratio through proved equal-size fibers of ordered injective samples, rather than leaving a result only for iid draws or a different probability space.

The entire original problem is the source's asymptotic Corollary 1.2. The source's exponential finite estimate and positive fraction of small singular values are stronger supporting results. Proving the documented weaker polynomial probability bound proves the whole original target; it is not a partial or conditional formalization. The guide explicitly declines to advertise those stronger source theorems as formalized.

## Complete mathematical proof audit

The nine-module linear-algebra/probability core is explained in `core-1.md`; I checked its final changed files again. The modifications reuse `norm_smul_inv_norm`, replace a deprecated matrix-action lemma, omit unused section variables and remove unused tactic arguments. They do not change the mathematical objects or theorem scope. The following checks cover the complete path through the new final assembly.

1. **Actual deletion statistic and simultaneous witnesses.** `defect` is a proved minimum over deletion sets, not a definition containing the desired conclusion. Coordinate restriction proves its one-column Lipschitz bound and reindexing invariance. `FiniteCommonReservoir` extracts actual finite span coefficients for every reconstructible center, builds dependence vectors with an identity block on the distinct centers, and proves the witness map is expansive by those coordinates. The shared reservoir is a disjoint summand of the column-index type. Rank-nullity and Bessel then imply the half-count lower bound without assuming error orthogonality, independent center success, bounded coefficients, or disjoint reservoir choices between centers.

2. **Regularized covariance filter.** Signed sparsity proves `Sigma <= s*D` for `D_i = E[u_i^2]+1/k`, with strict diagonal positivity in positive dimension and trace `s+1`. The spectral estimate is applied only to the PSD conjugate `D^(-1/2)*Sigma*D^(-1/2)`. The noncommuting original covariance/diagonal factors are handled by explicit similarity and trace identities. Singular covariance and zero coordinate incidences are allowed; no false Euclidean contraction of the nonsymmetric filter is assumed.

3. **Ideal finite experiment.** `SignedState` includes both signs of each original column and an absorbing zero. `coordinateChoice` has weight `v_i^2/s`. `coordinateDraw` assigns weight `p(a)*u(a)_i^2/D_i` to each sampled column and assigns its proved nonnegative remaining mass to zero. The orientation identity explicitly treats all signed-entry possibilities; no sign symmetry of the column law is assumed. The resulting mean is exactly the transition matrix from the covariance filter. `FinitePaths` tracks post-transition state number `j+1`; `IdealEstimator` matches those indices with the binomial coefficients. Conditional on each center, the `b` paths are an actual iid product law. The exact variance-of-average identity and uniform path norm bound yield the displayed squared-error bound. `exists_estimator_parameters` chooses positive finite `L,b` using only `s,eta`, before dimensions or the matrix law. Markov gives success at least three quarters.

4. **Real reservoir experiment and domination.** The actual transition uses half a point mass at zero and half the first hit of a requested nonzero coordinate in a fresh retained chunk; a missing hit also gives zero. This refinement is valid: zero is in every reservoir span and supplies additional zero mass. The first-hit weight is proved exactly, including zero incidence. Under `c <= 1/2` and `c <= ell/(2*k)`, both zero and nonzero outcome weights dominate `c` times their ideal weights. `CoupledPaths` proves the iid input marginal, state marginal, and input-dependent span support. Domination is iterated on nonnegative unnormalized weights for paths and then independent path batches. It never claims that conditioning on a sequence of hits preserves the ideal law. `reservoir_success_probability` consequently concerns the actual sampled-column span, with all auxiliary state randomness removed.

5. **Common reservoir and uniform mean.** `FiniteBlocks` proves product-law regrouping and relabeling. `IIDMean` counts reconstructible centers and uses only linearity of expectation, so the dependence caused by their shared reservoir is harmless. It includes leftover columns explicitly and transports the resulting statistic to exactly `r` iid draws. In `UniformMean`, `J=b*L`, `m=floor(r/2)`, and `ell=floor((r-m)/J)` satisfy the required size inequalities once `r >= 4J`. The proved aspect bound yields `c=beta/(8J) <= ell/(2k)` and `c <= 1/2`. The constants `rho=c^(L*b)/8 > 0` and `R=4J` are chosen before `k,n,r,M`. The arithmetic combines success at least `(3/4)*c^(L*b)`, the half-count witness bound, and `r <= 3m` to obtain `E[defect] >= rho*r`. The README constants match these actual declarations.

6. **Without-replacement sampling.** `FiniteVariance` proves the iid variance bound at most `r` for a coordinate-one-Lipschitz statistic by the total-variance identity and induction. `FiniteSampling.repair` keeps an iid draw if it is fresh and otherwise samples uniformly among fresh indices. Both marginals and its exact mismatch expectation are proved, then composed to give an iid/uniform-embedding coupling with expected Hamming cost `r*(r-1)/(2n)`. `ProbabilityTransfer` shows that an event with zero deficiency forces either a large iid deviation from its positive mean or a large repair cost. Chebyshev and Markov give exactly `4/(rho^2*r)+(r-1)/(rho*n)`. The positive `n,r,rho` assumptions required for these divisions are supplied in the final application.

7. **Exact subset bridge and limit.** `FiniteSubsets.rangeFiberEquiv` identifies each ordered-range fiber with bijections onto that subset and proves its size is `r!`. The factorial cancels from both sums and cardinalities, giving the literal uniform subset ratio. `SubsetDefect` proves zero ordered deficiency on the advertised strict singular-value event using a genuine coefficient-space isometry. `Asymptotics` derives the eventual aspect lower bound with `beta=1/(2C)`, sample-size divergence, and `r/n -> 0`. `Solution` applies the uniform mean theorem only on an eventual set where sparsity and all positive-size conditions hold, bounds the exact tail by two quantities tending to zero, and squeezes using its proved nonnegativity. This closes every reduction to the frozen exported proposition.

I found no unjustified primitive, circular certificate, hidden false hypothesis, restricted family substituted for the original target, or lost probability/quantifier in this chain.

## Reuse, API, guide and attribution

I searched the pinned Mathlib and relevant repository examples during selection and core review. The proof reuses its Euclidean norm and isometry machinery, finite-dimensional rank-nullity, orthonormal bases and Bessel inequality, PSD congruence and Hermitian spectral theorem, finite sums/products and geometric identities, finite embedding/permutation cardinality, and filter limits. It avoids introducing a new ordered-eigenvalue framework when the deletion statistic suffices. Namespace placement and module division separate probability, linear algebra, reconstruction, sampling and assembly cleanly; the single advertised declaration has the exact frozen type.

The local finite real-weight `Law` representation overlaps with Mathlib PMF functionality, but every operation and concentration bound is proved from normalized finite sums, and the final sampling law is connected directly to the frozen real ratio. The README now explicitly explains this choice and does not advertise it as a replacement for Mathlib's general probability API. That resolves the documentation request from `core-1.md`. The optional normalization reuse request is also implemented. Earlier lints/deprecation warnings are absent from the final build I observed; no lint suppression or trust weakening was used to achieve this.

The guide describes the actual regularization, absorbing-zero/no-hit refinement, constants, polynomial tail, retained inputs and exact subset bridge. It distinguishes the entire original asymptotic target from the stronger unformalized source rate and separates local compilation from the fresh Linux gate. Mathematical-resolution credit remains with Sidney Holden; Huang, Rudelson and Tikhomirov retain conjecture and prior-result credit. OpenAI Codex agent implementation and independent AI review are disclosed separately. No human or source-author endorsement, sharp-rate claim, or computation-based proof is asserted. The project retains its Apache 2.0 license. The original canonical page and solution sources are unchanged at this snapshot.

## Independent local verification evidence

I independently ran `lake build Solution Challenge` with Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. It succeeded with 3233 jobs. The only reported warning was the intentional independent Challenge placeholder. I then ran my own `verification/FinalReferee1.lean`, which checks the exported theorem type and prints transitive axioms for the full theorem and fifteen supporting declarations spanning the proof. Every list is exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, custom axiom or native-evaluation axiom occurs. Source scanning found no `sorry`, `admit`, custom axiom, unsafe implementation or Challenge import in the Solution source graph. The only explicit proof resource option is a local heartbeat increase.

| Evidence actually inspected | SHA256 |
| --- | --- |
| My `verification/final-referee-1-build.log` | `23fc7fa395f5726996ff22add4e728944a60b5ab94cc671d5f947196404433bd` |
| My `verification/FinalReferee1.lean` | `87fc9fc8f88ee1a65744c4863a8b174362b358b4d2193f39457fa248786a7377` |
| My `verification/final-referee-1-axioms.log` | `2177491c1ec5ac8393f44fac7270406368ee74e592ff5a6e826f8c6fbbe769da` |
| Author `verification/local-build.log` | `6fcfb9ddfdc58fa86dcfb07feeeb7ce339bdd6e34f79259686b7f5f7acd7e3e3` |
| Author `verification/Check.lean` | `4547c22435487677d13f1f3d1628e2e3f5a1c7a1ed9e97b742f0581831fac751` |
| Author `verification/axioms.log` | `ffc1dee47fbb9f1dfa6abaa7b0d890f71ef43aaa336ffa533c4773518c05445f` |

I also independently checked the author's build and axiom logs rather than relying on a reported PASS. My import-closure and per-file hash comparison is retained in `verification/final-referee-1-hash-check.log`. All of these runs are local macOS checks using available build artifacts; none is represented as a fresh Linux verification.

## Remaining publication gates

The mathematical/source verdict is final for this exact snapshot. The fresh sandboxed Linux verification, its Comparator result and controls, artifact provenance and source-hash match remain pending and must be audited in an addendum before this report can support final status promotion. Any later canonical/catalog promotion also requires a documentation addendum once its actual bytes exist. A second independent final referee is required separately by the repository protocol; this report is one independent referee's result and does not claim another agent's work. No remaining mathematical proof task or original-target subcase is excluded from this approval.

## Committed proof and initial metadata addendum

The proof and initial metadata were subsequently committed as `810014241511510dce72a418e1ba80a4cd4c7a7e`. I independently read each of the 36 proof inputs from that Git commit and compared it to both the current file and the frozen proof manifest: all match. Thus the mathematical approval above also binds this immutable proof commit, without any reliance on a branch name or an author's statement that the sources were unchanged.

I read the complete committed `formalization.yaml`, SHA256 `0713c65d2894977c84f3e06a379d9947e8df682385c0c8a570ab88a0b308700d`. Its scope, source citations and hashes, two-coauthor attribution, no-endorsement disclosures, concrete sampling/norm semantics, and account of the proof changes agree with the reviewed implementation. Its `sorry_count: 0` is expressly scoped to the proof development, with the single independent Challenge placeholder disclosed. The permitted axiom list matches my audit. Its `whole_problem_verified: false`, `canonical_status: Solved`, and explicit fresh-Linux pending descriptions correctly preserve the outstanding mechanical gate. The initial metadata describes the full final reviews as pending because it preceded the signed final reports; those review-status descriptions should be updated when both final reports are finalized, without converting that update into a Linux-verification claim.

Verdict on this initial metadata: **APPROVE its mathematical scope, attribution and pending-verification disclosures.** No actual Linux run or artifact receipt has been inspected by this reviewer, and no successful remote run, publication or status promotion is claimed. The hash-comparison evidence retained in `verification/final-referee-1-hash-check.log` has SHA256 `1080a94c87c26a1a0ed1a82d098e9c40d2dc892fd46fd250dbc8ced81441d0f3`.

## 2026-09-29: fresh Linux evidence acceptance

**Verdict: APPROVE the retained fresh Linux verification evidence for the complete reviewed TR-07 proof.** This addendum supersedes the earlier descriptions of the Linux/Comparator gate as pending; those descriptions remain above as historical records of what had been available at each review phase. It does not claim that I personally executed the remote job or that a pull request has been submitted. Review of the actual later status-promotion documents remains separate.

I independently inspected the downloaded artifact for [GitHub Actions run 36544197412](https://github.com/marcusdavidwebb/OpenProblemsInNLA/actions/runs/36544197412), artifact ID `11022101809`, retained at `verification/linux-36544197412/`. Its receipt identifies repository revision `4aa20f0e6ad92037a616c81fa8b1d7f57abca2dc`, the exact TR-07 project, Lean 4.33.1 on x86_64 Linux, and result `comparator-accepted`. The source-lock SHA256 is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, matching the repository's actual `tools/lean/source-lock.json`; its checker source commit is `8d1b0c0545a77b40245e84705aa7d273e6c81e62`.

My independent integrity checks found:

- All **18** entries in the expanded evidence checksum manifest match their actual files, including the three retained public GitHub API responses added after the original artifact download.
- All **13** payload files inside the original ZIP match the retained extracted files byte for byte; the ZIP CRC check has no error.
- The ZIP SHA256 is `4ca8da9a1849c52f054b77c4706131df4b78e1c60617c7898c267beafad660d3`, equal to the download and published-artifact digest recorded in `PROVENANCE.json`.
- All **69** receipt input hashes match files read independently from the receipt's immutable Git revision.
- Every one of the **36** frozen proof inputs matches the receipt, the current main-workspace file, the approved proof manifest, and the already reviewed proof from `810014241511510dce72a418e1ba80a4cd4c7a7e`. Definitions, Challenge, Solution, toolchain, dependency manifest and Comparator configuration are unchanged. Thus this is evidence for the reviewed full theorem, not another statement or an earlier partial proof.

I read the actual logs, not only the receipt's success field. `comparator.log` shows fresh compilation of Definitions/Challenge and every project proof module in a temporary project, separate exports of the same advertised theorem, followed by “Lean default kernel accepts the solution” and “Your solution is okay!”, with exit status zero. The deliberate placeholder warning occurs only in the independent Challenge. Dependency setup records the pinned Mathlib commit and all manifest revisions; the Mathlib cache log concerns dependencies, while the project modules themselves are visibly rebuilt. The receipt explicitly says semantic review is not performed by the command; the full semantic approval is the independent review above.

The controls were also inspected individually. All five Comparator regression cases have the expected outcomes, including rejection of a statement mismatch and an illegal helper axiom. The three actual default-kernel/quotient controls accept the honest inductive-and-quotient fixture, reject a raw proof of the wrong type, and reject the quotient post-check mismatch. The two additional negative fixtures reject `sorryAx` and the generated native-decision axiom, each at the expected illegal-axiom stage with exit status one. The user-service probe succeeds. The sandbox log shows separate build/export confinement, denied writes outside the permitted build area, read-only export, private namespaces, denied host/AF_UNIX communication, absent effective capabilities, `no_new_privs`, rejection of nested namespace writes, and rejection of all four unsupported/permissive option probes. The sandbox control exits successfully after verifying its fixtures are unchanged.

| Retained evidence | SHA256 |
| --- | --- |
| `artifact.zip` | `4ca8da9a1849c52f054b77c4706131df4b78e1c60617c7898c267beafad660d3` |
| `PROVENANCE.json` | `f6897729bcd9362c8c9f997251e7786d1b107fe30cdb2afc3e68ef23f964e7f9` |
| `SHA256.json` | `6ab34e7c2c2437923f2ec6ce6e80ceb18d48043c933d0694f0f1f929593e57bc` |
| `GITHUB_RUN.json` | `fd959c7bb639b71046f76015266db341adac7c40f313521f02b5b899272e43f3` |
| `GITHUB_ARTIFACTS.json` | `fcaa622747625a31a00cd29692b43283fec5a8c28930862cef0a073d13913281` |
| `GITHUB_JOBS.json` | `d7557ba514c2a924c425d7b76c7d15cedb455d2f9c61479168b9a6449011f398` |
| `verify-20260929T084153Z-3983/result.json` | `5304e20473a8f639262f778f523a2d79fcfc1fc831176cdd68bfa2c6812be28c` |
| `verify-20260929T084153Z-3983/comparator.log` | `bbdb47c0c3f6a9651918488270e8ab6ce688a701e412ba4b4a28c54911b592fd` |
| `verify-20260929T084153Z-3983/comparator-controls.log` | `21ef91e9ba01c72da55a07989c17960619bd4ed8d89bf2937369d74ae1c05729` |
| `verify-20260929T084153Z-3983/kernel-controls.log` | `ac5884a6a9aab533b23369a1a9a4e453f745264bbaeb2e13d60d94569c45a361` |
| `verify-20260929T084153Z-3983/sandbox.log` | `9a746097605b57aa5fada39d8c5f3ea10eb24bcb9602a21ecaf5600a9f97760b` |
| `verify-20260929T084153Z-3983/negative-sorry.log` | `41768152f0c20810d188987f7074ac19170906c530d426a8ba8412263f6f66c6` |
| `verify-20260929T084153Z-3983/negative-native.log` | `6beb9e23e6e6a1ead30bbc8a657e08a6465b941cba4fe7234d1ad54c7c73ff56` |

I also inspected the retained public API responses directly. `GITHUB_RUN.json` records a completed successful push run at the stated revision. `GITHUB_ARTIFACTS.json` connects artifact `11022101809` to that run and revision and publishes the exact digest I computed from the retained ZIP. `GITHUB_JOBS.json` shows the TR-07 verification job `109326693985` on `ubuntu-24.04`, with every executed step successful, including fresh sandboxed statement, axiom and kernel verification. The separate workflow-level `checker-controls` job is recorded as skipped; this is not described as a passed job. The per-project control execution is independently evidenced by the actual control logs audited above.

Provenance limitation: my own live requests to the public GitHub endpoints failed because the web tool could not access them and the shell environment could not resolve the host. I therefore do not claim that I independently downloaded those API responses. Independent reviewer `/root/environment` directly confirmed to me that it separately fetched the unauthenticated run, artifact and jobs endpoints and verified the successful revision, published ZIP digest, linked artifact and Ubuntu verification job; that reviewer records its live check in its own addendum. My independently performed checks cover the retained API contents, actual ZIP, all extracted logs, receipt and source hashes. The combined provenance record distinguishes that separate live API check from my direct artifact audit rather than treating an author's reported PASS as proof evidence.

No proof file was edited for this audit. The complete original-target mathematical approval stands, and the retained Linux evidence now satisfies the previously outstanding mechanical-evidence review within the stated provenance scope. A follow-up addendum will assess the exact canonical, catalog and metadata promotion changes when those files are ready.

## 2026-09-29: final publication and status-promotion approval

**Verdict: APPROVE the actual promotion documents and preservation of the full original target.** This addendum closes the publication-document gate left pending above. Together with the complete mathematical review and accepted fresh Linux evidence, it supports the status `Lean verified` for the entire original TR-07 asymptotic theorem. It does not assert that a PR has already been opened or accepted.

I independently compared the current canonical page against published base `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`: its complete text from `## Problem statement` onward is byte-identical, as are both original solution sources and the entire permanent-ID registry. The promotion changes retain TR-07's identity, path, original theorem and mathematical attribution. The generated indexes change exactly one entry from solved to Lean verified (41 solved and 65 Lean verified), leaving the 110 open-target count and 217 retained-entry total unchanged. I rechecked all 36 current proof inputs against the approved manifest; every hash still matches.

I read the actual canonical verification section, resolution-archive addition, formalization guide, metadata, verification/review guides and proposed PR text. They accurately distinguish the whole original asymptotic theorem from the manuscript's stronger unformalized finite exponential estimate and positive-fraction theorem. They record the actual successful run, immutable proof revision, standard axioms and independent nonauthor AI reviews, preserve Sidney Holden's mathematical-resolution credit and the prior authors' credit, and make no human-review or source-author-endorsement claim. The metadata's `whole_problem_verified: true` and canonical `Lean verified` status are now supported by the separately audited mechanical and semantic evidence. Local file/directory destinations in the reviewed Markdown resolve. I independently ran the manifest validator with the prepared Python environment; it reported `Manifest schema and comparator coverage: PASS (1 declarations)`.

I also inspected the renderer diff, generated TeX and both pages' extracted PDF text. The renderer change only adds TR-07 to the existing list whose footer identifies a verification date rather than a literature-search date. The resulting footer says `Verification check: 2026-09-29`; the full original mathematical statement is present on page 2. I did not perform an independent graphical layout inspection. The retained packaging log explicitly attributes that visual inspection to a coauthor, preserves the earlier failed render and its successful correction, and records successful permanent-ID/catalog checks, 17 ID tests, 3 status tests and 11 rendering tests. These are packaging checks, not substitute Linux proof evidence.

The exact final packaging bytes I reviewed are bound below. Paths are relative to the repository root unless their short descriptive labels identify the TR-07 Lean-project guides already named above.

| Reviewed publication input | SHA256 |
| --- | --- |
| Canonical TR-07 page (`randomized-and-low-rank-approximation/TR-07/README.md`) | `1789276f7e6c84f6d419eb6501ebd964795ab16a13a6c568400942937cdc9893` |
| Resolution archive (`RESOLVED.md`) | `335069c6e566939196c808d541f996d4f1807199c600496a1fa65301ed51b45d` |
| Root README (`README.md`) | `9ead0ea4532948f7e7f9b5447427bbb822ae2fb05e5c4ef7de9a0df2d8c8a029` |
| Catalog (`CATALOG.md`) | `096747c3c482c75a96977d572b6691e8c399c553ca72581914cc1f7db52d41a2` |
| Category README (`randomized-and-low-rank-approximation/README.md`) | `5e21f4a66b60462017902af946c91d5d415e8709ce845e5c6719bfdde841f30e` |
| Permanent ID registry (`problem_ids.json`) | `d7f9925a483d40030ef266917bc8e413dac6d45530ad5515da506ffe9583e763` |
| Generated problem TeX (`randomized-and-low-rank-approximation/TR-07/problem.tex`) | `e4c0491e40fa7d52d59867ca2b3f9de0a36e581551452db00a99172fb1d29de8` |
| Generated problem PDF (`randomized-and-low-rank-approximation/TR-07/problem.pdf`) | `92f3dffb20028c9ca879df65d4e60b79d39531d7a9282b5c3ee78bbf42860b95` |
| Renderer (`tools/render_problems.py`) | `a8d536c2b20d349c7dd104f7e03f4054e3ad7b8fbd7359cd4a509c8a2e7eebf9` |
| Formalization guide (`randomized-and-low-rank-approximation/TR-07/lean/README.md`) | `73d7251e5947a0ddeb6a8cba64cd36d731646358b08d4babff1063180a9dd91e` |
| Formalization metadata (`randomized-and-low-rank-approximation/TR-07/lean/formalization.yaml`) | `2c994ca0c2e2d7d6d53d9cefcf13394f805709e26d94d609e7be48dd933a32eb` |
| Proposed draft PR (`randomized-and-low-rank-approximation/TR-07/lean/DRAFT_PR.md`) | `7910de4514fb00d9ed730e2dfc76edc3b29236f32e75abeb4047f7ffb165af50` |
| Review guide (`randomized-and-low-rank-approximation/TR-07/lean/reviews/README.md`) | `f28c74529d5026af422c7b9dbe506d75463afed70de905166114351cae56a67f` |
| Verification guide (`randomized-and-low-rank-approximation/TR-07/lean/verification/README.md`) | `2199f6c6362d29e7a0a3a5cae6fa9aea7532fdea24ac25cf9d3cebd977edfed9` |
| Packaging check log (`randomized-and-low-rank-approximation/TR-07/lean/verification/packaging-checks.log`) | `a730d6160c2bb0e9977f02f961eb4eace47338f4ca8d19cb478dcd8f8d01b747` |

I remain an independent nonauthor AI reviewer of the TR-07 definitions and proofs. I edited only my review record for this audit. No mathematical, source-integrity, attribution or publication-scope issue remains in the reviewed snapshot.
