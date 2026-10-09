# TR-07 independent final review 2

**Reviewer:** OpenAI Codex AI agent `/root/environment`.  
**Independence:** I authored no mathematical definitions or proofs in this project. I read the sources and ran independent checks; I did not substitute another agent's claimed result for that work. This is AI review, not human peer review or source-author endorsement.  
**Mathematical verdict:** **APPROVE the complete original TR-07 theorem at the exact snapshot below.** All bridge premises are discharged in `Solution.lean`; no requested mathematical correction remains.  
**Verification status at this phase:** Local build and transitive axiom checks pass. Authoritative fresh Linux Comparator/kernel verification and final promotion-document review are still pending. This mathematical approval alone does not authorize describing the result as Lean verified under repository policy.

## Exact reviewed scope

I reviewed the canonical problem and complete `solution.tex` at base
`80c0e3e638b2f26dcb3a00353651fc3d2215dd65`, as recorded in
[statement review 2](statement-2.md). The source hashes remain:

| Source | SHA256 |
| --- | --- |
| Canonical `../README.md` | `1f2b4c9bfd606f49d2c522483a7375cff104744e7a540db1613bb01f91a281d0` |
| Complete `../solution.tex` | `207eb87c6b47d3a3a1a529c49b7c5a4dcaf099a942d60fdc1b9b5e3285aae7a0` |
| `../solution.md` pointer | `307e8b419a4eb453e789120d86e1344b2aecaf8a8ce759f87d9585a470496fee` |

The statement-freeze commit is `1b27d9f89eb41d1b7a2adfdfb33d870a8d6f31a5`. Proof files were inspected as the completed working-tree snapshot. Their complete hash binding is [verification/PROOF_SHA256.json](../verification/PROOF_SHA256.json), SHA256
`a499fc82cdebbe416686d7ecda0f105b50bad7bde1b9ba5fbdae71815ee4832e`.
I independently checked all **36 entries** against the actual file bytes and checked that the manifest includes every project mathematical module, Challenge, Solution, Comparator config, toolchain, Lake config, and dependency manifest.

The Solution's complete local import closure contains **31 modules**, all read in full across this review and [the earlier core review](proof-core-2.md). I reread every previously reviewed module whose hash changed. Those changes remove unused instances/simp arguments, replace a deprecated matrix-action API, or use Mathlib's existing normalization lemma; no mathematical hypothesis or conclusion was weakened. All modules newly added after the core report, including `FirstHit`, `CoupledPaths`, `ReservoirStep`, `ReservoirReconstruction`, `IIDMean`, `UniformMean`, `SubsetDefect`, `Asymptotics`, and `Solution`, were read in full.

Additional reviewed and inspected-file bindings are:

| File | SHA256 |
| --- | --- |
| `README.md` proof guide | `c2a7b570f77413bd4aa2f05a0f1c9db2178ce8998e431e0af6514390db6f6a35` |
| `NUMERICAL_TARGETS.md` | `4780404e41c13668ee57f7c4cff51a4bc9a09fbe1f7ea1f30b6fa936fd7c7a08` |
| `verification/Check.lean` | `4547c22435487677d13f1f3d1628e2e3f5a1c7a1ed9e97b742f0581831fac751` |
| `reviews/final-2-build.log` | `9e1bea833c70caacb32301f2c27c51b117c02c0762332ad48b0b982c46af3828` |
| `reviews/final-2-axioms.log` | `a33f8f270e2d461bee707745d6d33c2041dc48056ab0eb09e506c0f949747598` |

The definitions and Challenge hashes are unchanged from the approved boundary:
`d80638b68ed9fc06f3013edfefb743965de664c4bab312d03e239ee25fc80233`
and `0371225eaf7dfcf5691590cfcdd8bacbece0ceddb8716b04c01cd365ee3202cc`.

## Entire-target fidelity

The exported theorem is exactly
`NLA.TR07.random_column_subsets : NLA.TR07.SolvesTR07`. I independently asked Lean to print `SolvesTR07` and check this declaration, and inspected the resulting full quantifiers in my axiom log.

The theorem includes every fixed `s >= 2`, finite real `C >= 1`, admissible dimension sequence, deterministic signed sparse matrix sequence, and fixed positive threshold. It allows arbitrary support intersections, arbitrary signs, and repeated column values. The matrix action and both vector norms are the literal rectangular product and Euclidean norms. The singular value is the infimum over the entire unit sphere. The probability is the exact strict-tail cardinality ratio over all unordered subsets of column indices of the required size.

There is no reconstruction oracle, conditional-probability surrogate, extra covariance assumption, restricted dimension family, or favorable-support premise in the exported theorem. `r <= n` states the domain of the original sampling experiment. Eventual sparsity permits irrelevant initial dimensions below `s`. The nonvacuity analysis from statement review still applies, and the proof now derives eventual `r > 0`, the aspect lower bound, and `r -> infinity` from the original ratio limit. Empty-sphere and zero-division conventions therefore cannot manufacture the asserted limit.

This is the **entire original asymptotic target**, source Corollary 1.2. The source's stronger exponential finite tail and positive-fraction singular-value theorem are not part of the advertised result. The proof guide makes that distinction accurately; the formalization does not claim those stronger auxiliary conclusions.

## Proof audit and resolution of interim obligations

The probability, covariance, deletion, and ideal-estimator core findings in the interim report remain valid at the reviewed final hashes. Every assembly obligation identified there is now discharged:

1. **Actual reservoir inputs and unconditional domination.** `FirstHit` proves the exact first-hit distribution and its regularized geometric lower bound. `ReservoirStep` mixes a zero outcome with the first hit, with no-hit also returning zero. Its complete outcome law dominates the ideal law pointwise. `CoupledPaths` retains every actual independent block, proves its IID input marginal and the state-path marginal, and composes domination without conditioning on hits. This avoids the path-dependent conditioning error highlighted in the statement record. The changed no-hit convention is harmless and explicitly explained in the final proof guide.
2. **Actual-span witnesses.** A positive-mass transition state is proved to lie in the span of the block that produced it. This property is carried through all retained paths, and `reconstruction_mem_span` puts the averaged binomial estimator in the span of the actual reservoir columns. Ideal reconstruction success is transferred to this concrete `Reconstructible` event, not left as an abstract certificate premise.
3. **One shared reservoir and constants independent of dimension.** `IIDMean` computes the expected number of good centers by linearity, keeping a common reservoir and without assuming independent success events. The deterministic identity-block witness lemma yields the expected deficiency. `UniformMean` chooses positive `L,b` before dimensions and entries, puts `J=b*L`, `R=4*J`, `c=beta/(8*J)`, and `rho=c^(L*b)/8`, and proves all floor/count bounds needed to fit the centers and blocks. The lower bound `r <= 3*floor(r/2)` together with success factor `3/4` gives the displayed conservative `rho`. All dependence on the fixed parameters is in the correct quantifier order.
4. **The original subset event.** `SubsetDefect` transports coefficients by an actual bijection between an ordered embedding and its range. The unit-sphere infimum bound implies `Good`, which makes the deletion minimum zero. Single-coordinate replacement gives the exact Lipschitz premise used by `ProbabilityTransfer`. Its collision coupling has both exact marginals and the checked mean cost, and the uniform range law follows from equal fibers of cardinality `r!`. Thus the resulting finite probability estimate applies to the frozen `subsetTail`, including multiplicities of identical column values.
5. **All limits and final assembly.** `Asymptotics.aspect_ratio_bounds` proves eventual positive sample size, `r >= k/(2*C)`, and divergence of `r`. Reciprocal limits give `r/n -> 0`. `Solution` takes `beta=1/(2*C)`, intersects the actual eventual hypotheses, invokes the proved finite expectation and subset bounds, and squeezes the nonnegative probability by a function tending to zero. No asymptotic estimate remains an input assumption.

The infimum bridge uses `csInf_le` with an explicit lower bound and the normalized-vector member, so it does not misuse a conditional infimum on an empty or unbounded set. The simultaneous-witness argument uses rank-nullity and Bessel rather than assuming eigenvalue interlacing. The regularized nonsymmetric covariance filter is reduced to a Hermitian PSD matrix by proved diagonal conjugation, so no Euclidean contraction of a nonsymmetric matrix is assumed.

I found no unresolved mathematical, endpoint, norm, sampling, or scope defect in the final proof.

## Reuse, presentation, and attribution

I checked relevant pinned Mathlib APIs, including finite PMFs (`PMF.ofFintype`), variance inequalities, Euclidean normalization, Bessel's inequality, rank-nullity, and the Hermitian spectral theorem. The project reuses the substantial analytic and linear-algebra infrastructure. Its finite real-weight `Law` type is a reasonable local choice for a target expressed as a real finite count ratio: all normalization, sampling, variance, and coupling facts are proved, with no new trusted probability API. The guide explains this choice and does not advertise it as a replacement for Mathlib's general probability library.

Module names and comments identify the proof roles. The guide states the simplified auxiliary constants and proof-route changes, accurately distinguishes local compilation from authoritative verification, and credits Sidney Holden for the mathematical resolution and Huang, Rudelson, and Tikhomirov for the conjecture/prior results. Formalization authorship and independent AI review are disclosed separately. No human or source-author endorsement is claimed.

## Independent mechanical checks

My retained [build log](final-2-build.log) records an independent
`lake build Solution Challenge`: **PASS, 3233 jobs**, with only the deliberate `Challenge.lean:6:8` placeholder warning. The earlier lint/deprecation observations in the core report are resolved in this final build.

My retained [axiom log](final-2-axioms.log) records an independent Lean invocation printing the complete target and checking twenty declarations, including the exported theorem, both reconstruction laws, path marginals/domination, shared-reservoir expectation, the subset bridge, and all limiting steps. **Every transitive axiom closure is exactly `[propext, Classical.choice, Quot.sound]`.** There is no `sorryAx` or native-execution axiom in the proved theorem.

My [preflight record](final-2-preflight.log) confirms all 36 manifest hashes, exact proof input inventory, the complete 31-module local Solution import closure, absence of Challenge from that closure, and independent `harness.validate_project` success. The configuration names distinct Challenge/Solution modules, compares the complete exported theorem, contains no replaceable definition holes, and permits only the standard three axioms. Source scans found no admitted proof, added axiom, unsafe foreign implementation, or trusted native execution in the Solution tree.

I checked the actual local toolchain as Lean 4.33.1 and the Mathlib checkout as clean at `0df444a360eaa60ab8c11dca51a86af692955474`. I also read the root author's `verification/local-build.log`, `verification/axioms.log`, and `verification/Check.lean`; these agree with, but are separate from, my own reruns. These are macOS developer checks, not the required fresh Linux sandboxed run.

## Pending evidence and promotion gate

The mathematical and local mechanical review is complete. A later addendum must inspect the actual fresh Linux receipt, sandbox/bootstrap/negative controls, Comparator and kernel logs, and their binding to this exact proof snapshot. Final metadata, canonical status changes, and public verification links also require that evidence-based review. Until that addendum is present, this report does not approve `Lean verified` status or claim that the Linux gate has passed.

## Committed-source and pending-status metadata addendum

The proof was committed during this review as
`810014241511510dce72a418e1ba80a4cd4c7a7e`. I independently compared every one of the 36 manifest entries with both the corresponding committed Git blob and the current file; all three versions agree. The canonical problem and complete informal solution still have their original source hashes above. This supplies an immutable proof revision without changing the mathematical approval or the pending Linux gate.

I read the subsequently supplied `formalization.yaml`, `verification/README.md`, and `DRAFT_PR.md`, and independently ran the repository manifest validator: **schema and Comparator coverage PASS for the one exported declaration**. The metadata accurately records the complete scope, both coauthors, both independent nonauthor reviewers, permitted axioms, source attribution, regularized proof route, simplified constants, and exact subset semantics. At this phase it conservatively keeps `whole_problem_verified: false` and canonical status `Solved`. Its references to final reviews still being pending should be updated once both final reports are retained; that is a documentation status update, not an unresolved mathematical defect.

The draft PR correctly presents the full proof as awaiting fresh Linux verification and preserves the original ID, path, and target. I have not independently verified its remote publication status and do not claim that it has been published or that any Linux run has occurred. The reproduction instructions and verification guide keep the local and authoritative gates separate.

| Additional reviewed file | SHA256 |
| --- | --- |
| `formalization.yaml` | `0713c65d2894977c84f3e06a379d9947e8df682385c0c8a570ab88a0b308700d` |
| `verification/README.md` | `0f883d94e71fdc950c8f4a7816351536d1d94a91cb30111a6f83b02c3445bf60` |
| `DRAFT_PR.md` | `4a08c80ecdb870ea8680fcc251fbf13d918466fccc3acf852b2a790e02fec1b4` |
| `reviews/final-2-preflight.log` | `4ccdf80c3a1137e0d425e6bb36d199b085d6e46ccf93e91204ed286d9a31af89` |

No Linux evidence or status-promotion approval is supplied by this addendum. The pending gate immediately above remains in force.

## 2026-09-29: authoritative Linux evidence and publication approval

**Verdict: APPROVE the retained fresh Linux verification and the final `Lean verified` promotion for the entire original TR-07 target. This addendum supersedes all earlier pending-Linux, pending-evidence, and pending-promotion wording in this report.** Those earlier paragraphs remain as historical records of the evidence available during each phase. No mathematical proof was changed for this review, and this approval does not claim that a pull request has already been submitted.

I independently read the actual artifact and all its logs in the main repository workspace. I also independently fetched the unauthenticated public GitHub API run, artifact, and jobs endpoints; these requests succeeded. [Run 36544197412](https://github.com/marcusdavidwebb/OpenProblemsInNLA/actions/runs/36544197412) is completed with conclusion `success`, at revision `4aa20f0e6ad92037a616c81fa8b1d7f57abca2dc`. Artifact `11022101809`, named `lean-TR-07`, is linked to this exact run and revision. GitHub publishes its SHA256 as
`4ca8da9a1849c52f054b77c4706131df4b78e1c60617c7898c267beafad660d3`,
which equals my digest of the retained original ZIP. Verification job `109326693985` ran on `ubuntu-24.04`; every step of that job succeeded, including preparation of unprivileged Linux isolation and the fresh sandboxed statement, axiom, and kernel check. The separate workflow-level `checker-controls` job was skipped; I do not count it as a passed job. The per-project controls were actually executed, as their logs demonstrate below.

The independently fetched API fields agree with the retained `GITHUB_RUN.json`, `GITHUB_ARTIFACTS.json`, and `GITHUB_JOBS.json`. I verified all **18** entries of the final retained evidence checksum manifest and compared all **13** original ZIP payload files byte for byte with the extracted files. I verified all **69** receipt inputs against Git blobs from the immutable CI revision. Every one of the **36** frozen proof inputs agrees across the current source, original approved proof commit `810014241511510dce72a418e1ba80a4cd4c7a7e`, proof manifest, Linux receipt, and CI revision. The exact target, definitions, Challenge, Solution, configuration, and pins are therefore the previously reviewed ones. These independent checks are retained in [final-2-linux-checks.log](final-2-linux-checks.log), SHA256 `d5b46752565fa83bafbe9a99355577a8b89d34c4f4aa53324d100ddbbff81430`.

The receipt records `comparator-accepted`, the correct project and exported theorem, no definition holes, and only the three permitted axioms. Its tool receipt identifies Lean 4.33.1 on x86_64 Linux and the pinned Forsythe checker commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. The source-lock SHA256 `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b` matches the repository file. The checker tools and workflows are unchanged between the originally reviewed proof commit and the CI revision.

I inspected every artifact log, including bootstrap, dependency retrieval, Mathlib cache, service probe, sandbox, all controls, and the actual candidate Comparator run. The dependency log checks out the pinned Mathlib and transitive revisions; the project modules are then visibly rebuilt in a fresh temporary project. The candidate log separately builds and exports Challenge and Solution, with the deliberate placeholder warning only in Challenge, and ends with default-kernel acceptance, `Your solution is okay!`, and `EXIT_STATUS=0`. Thus the result is more than a cached local build or a success label.

All five Comparator regressions have their expected outcomes. The default-kernel controls accept the honest inductive/quotient fixture, reject the raw proof with the wrong type, and reject the quotient post-check mismatch. The separate negative fixtures reject `sorryAx` and the generated native-decision axiom, each at the illegal-axiom check with exit status one. The sandbox probes show private namespaces, no effective capabilities, `no_new_privs`, denied writes outside the allowed build area, read-only export, denied host/network/AF_UNIX access, and rejection of nested namespace writes and all four permissive/unsupported option cases. The sandbox UID is 1001. The service and bootstrap checks succeed. No expected rejection is being confused with a failure of the candidate theorem.

The retained evidence binding is:

| Evidence file under `verification/linux-36544197412/` | SHA256 |
| --- | --- |
| `artifact.zip` | `4ca8da9a1849c52f054b77c4706131df4b78e1c60617c7898c267beafad660d3` |
| `PROVENANCE.json` | `f6897729bcd9362c8c9f997251e7786d1b107fe30cdb2afc3e68ef23f964e7f9` |
| `SHA256.json` | `6ab34e7c2c2437923f2ec6ce6e80ceb18d48043c933d0694f0f1f929593e57bc` |
| `GITHUB_RUN.json` | `fd959c7bb639b71046f76015266db341adac7c40f313521f02b5b899272e43f3` |
| `GITHUB_ARTIFACTS.json` | `fcaa622747625a31a00cd29692b43283fec5a8c28930862cef0a073d13913281` |
| `GITHUB_JOBS.json` | `d7557ba514c2a924c425d7b76c7d15cedb455d2f9c61479168b9a6449011f398` |
| `verify-20260929T084153Z-3983/result.json` | `5304e20473a8f639262f778f523a2d79fcfc1fc831176cdd68bfa2c6812be28c` |
| `verify-20260929T084153Z-3983/comparator.log` | `bbdb47c0c3f6a9651918488270e8ab6ce688a701e412ba4b4a28c54911b592fd` |

The evidence checksum manifest binds the remaining individually inspected logs. The proof manifest remains SHA256 `a499fc82cdebbe416686d7ecda0f105b50bad7bde1b9ba5fbdae71815ee4832e`.

### Final publication documents

I reviewed the actual final canonical README, resolution-archive entry, metadata, proof guide, verification guide, review index, draft PR, generated index diffs, and generated TeX. I also read text extracted from both final PDF pages; I do not claim a separate raster/visual inspection. The narrow renderer change adds only `TR-07` to the existing set that labels formal-verification dates as `Verification check`, and the resulting PDF contains that accurate footer. It does not change the mathematical target or render other entries differently.

The canonical statement and its entire historical tail, beginning at `## Problem statement`, are byte-identical to the source revision. The original `TR-07` registry entry and canonical path remain unchanged. The generated catalog changes move exactly this retained entry from solved to Lean verified, changing the evidence counts from 42/64 to 41/65 without changing the open-problem count or any ID. The documentation links the exact immutable checked revision and public run, distinguishes prior informal AI review from kernel verification, preserves mathematical attribution, and expressly excludes the source's stronger exponential finite bound and positive-fraction theorem from the formalized scope.

The metadata now correctly sets `whole_problem_verified: true` and `canonical_status: Lean verified` for the complete original target. I independently reran the manifest validator after promotion: schema and Comparator coverage PASS. Both independent nonauthor mathematical reviews and their separate Linux evidence roles are accurately disclosed. No external human review or source-author endorsement is claimed. The draft PR describes a proposed contribution; this review does not assert that its submission has occurred.

These final packaging changes lie outside the unchanged 36 proof inputs. The Linux run proves the immutable proof snapshot; the correspondence between that snapshot and the later documentation is established by this review and the exact hashes below, not by claiming that CI checked documents written afterward. Paths in this table are repository-relative unless prefixed `lean/`, in which case they are relative to `randomized-and-low-rank-approximation/TR-07/`.

| Final publication file | SHA256 |
| --- | --- |
| `randomized-and-low-rank-approximation/TR-07/README.md` | `1789276f7e6c84f6d419eb6501ebd964795ab16a13a6c568400942937cdc9893` |
| `randomized-and-low-rank-approximation/TR-07/problem.tex` | `e4c0491e40fa7d52d59867ca2b3f9de0a36e581551452db00a99172fb1d29de8` |
| `randomized-and-low-rank-approximation/TR-07/problem.pdf` | `92f3dffb20028c9ca879df65d4e60b79d39531d7a9282b5c3ee78bbf42860b95` |
| `lean/formalization.yaml` | `2c994ca0c2e2d7d6d53d9cefcf13394f805709e26d94d609e7be48dd933a32eb` |
| `lean/README.md` | `73d7251e5947a0ddeb6a8cba64cd36d731646358b08d4babff1063180a9dd91e` |
| `lean/verification/README.md` | `2199f6c6362d29e7a0a3a5cae6fa9aea7532fdea24ac25cf9d3cebd977edfed9` |
| `lean/reviews/README.md` | `f28c74529d5026af422c7b9dbe506d75463afed70de905166114351cae56a67f` |
| `lean/DRAFT_PR.md` | `7910de4514fb00d9ed730e2dfc76edc3b29236f32e75abeb4047f7ffb165af50` |
| `RESOLVED.md` | `335069c6e566939196c808d541f996d4f1807199c600496a1fa65301ed51b45d` |
| `CATALOG.md` | `096747c3c482c75a96977d572b6691e8c399c553ca72581914cc1f7db52d41a2` |
| `README.md` | `9ead0ea4532948f7e7f9b5447427bbb822ae2fb05e5c4ef7de9a0df2d8c8a029` |
| `randomized-and-low-rank-approximation/README.md` | `5e21f4a66b60462017902af946c91d5d415e8709ce845e5c6719bfdde841f30e` |
| `tools/render_problems.py` | `a8d536c2b20d349c7dd104f7e03f4054e3ad7b8fbd7359cd4a509c8a2e7eebf9` |

The mathematical approval, real Linux verification, source binding, and publication-fidelity review are now complete. I approve the final status promotion at these hashes; no pending mathematical or verification gate remains in this report. This remains an independent AI-agent review, and publication/submission is a separate action.
