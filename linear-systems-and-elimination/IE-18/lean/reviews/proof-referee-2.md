# IE-18 independent proof referee 2

**Verdict: approve the completed mathematical implementation on the bound hashes.** The proof establishes the actual residual map twice, the maximum over the genuine eigenvalue list, the required second-square comparison, and a counterexample to the full original conjecture. No mathematical correction is requested. The authoritative Linux Comparator run and publication metadata remain separate pending gates.

Reviewer: independent Codex agent `/root/formal_review_standards`, 12 September 2026. The reviewer previously approved these frozen statements, did not author their definitions or the proof, and did not change mathematical code during this review. This is independent AI-agent review, not external human peer review or an official Tau Ceti service verdict.

## Reviewed sources and identity

The reviewer read the complete canonical IE-18 README and the entire Colbrook source manuscript, including its stronger parameter-family claim and excluded asymptotic question, and independently compared both files byte-for-byte with upstream commit `5adea969c17391693978ada2674d25bb5c3daeb1`. Definitions, Challenge, numerical targets, Proof, and Solution were read in full.

| Input | SHA-256 |
| --- | --- |
| `NLA/IE18/Definitions.lean` | `dc32a03d0ab95a1b3f41f864f90d30d56c3dd041330015caa059e253ff47b28d` |
| `Challenge.lean` | `97ad7cf8e2c3077d4cc52f587c9702627f06c8d915005804f044fd60c66ffd59` |
| `NUMERICAL_TARGETS.md` | `318f34ec1f88f111a83c1a6c869735ac2cc5640b5bdb34f89201e97607e9e890` |
| `NLA/IE18/Proof.lean` | `0244e39c88101ab7a998bb0c5da56549d668d46ae068e4fc2ef5067fabdf4f73` |
| `Solution.lean` | `d257fd0b3def07c4503f2e084407116661cac5e556d7fe46573c9f7f78c7c0c3` |
| Canonical IE-18 README | `ef32afd5788f56db1295284fba30de95e56478669f16513daed47535447ab7f0` |
| Full Colbrook `IE-18.tex` | `f7ebc6b6ebed015e24dfae48b0ed525fe67c99530a35ba66bed7d6ba44aa6b36` |

The [complete input manifest](../verification/referee-2/inputs.sha256.json) additionally binds the toolchain, Lake files, dependencies, and license. The statement hashes are unchanged from the review conducted before proof implementation. All three Solution theorem signatures match their respective Challenge signatures literally after whitespace normalization; see [the source identity check](../verification/referee-2/statement-identity.json). This direct comparison supplements, and does not replace, the future Comparator check.

## Full-target and definition fidelity

The review applied [Tau Ceti correctness and faithfulness](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/correctness.md) adversarially. `FourStepConjecture` retains every original quantifier: every dimension at least two, every nonzero real symmetric matrix, and exclusion of one from the actual matrix spectrum. It does not narrow the universal claim to diagonal matrices, positive definite matrices, contractions, selected eigenvalue certificates, or special initial vectors. Positive definiteness of both the witness and its complement is proved as an additional conclusion about the chosen admissible example.

The map uses the actual matrix-vector products with `A=I−M` and the coefficient `vᵀAv / ‖Av‖₂²`, returning zero explicitly at zero. Its actual composition is the four-step residual. The denominator agrees with the manuscript's `vᵀA²v` because the original matrix is symmetric. The norm is explicitly the square root of the sum of coordinate squares, avoiding the different default norm on a function type. `IsGreatest` expresses both attainment and the upper-bound property on all nonzero-vector amplifications; there is no empty-set or unbounded-set supremum default.

The pair maximum uses Mathlib's actual Hermitian eigenvalue list, retaining multiplicities, and every pair of distinct indices. The square of the scalar nonnegative norm, coerced to the reals, is the square in the original formula. Reversing a pair has no effect on that square. Real division implements the canonical zero-denominator convention. The numerical plan and proofs do not confuse this square with the additional square needed when comparing squared Euclidean norms.

The inspected library semantics include real `IsHermitian` as symmetry; `Matrix.PosDef` as strict positivity on all nonzero vectors together with symmetry; the actual matrix spectrum; the full eigenvalue list and its spectral range; the finite nonnegative-real supremum; and `IsGreatest` as membership plus an upper bound for every set member. The detailed initial semantic audit is retained in [statement referee 2](statement-referee-2.md). No hidden numerical assumption or vacuous logical substitute was found.

## Residual and admissibility proof

The proof starts by proving that the initial vector and first residual candidate are nonzero. It then computes the first actual denominator as `61/50`, derives coefficient `90/61`, and proves that the map returns `(-2,8,15)/61`. It separately computes the second actual denominator as `1381/93025`, derives coefficient `3140/1381`, and proves the second map value `(289,-756,1125)/84241`. The composition theorem rewrites by those two proved map identities. Neither candidate vector is accepted as a premise.

Both denominator identities are exact equalities with positive rational numbers. No zero-division convention can supply either result. The initial squared norm is proved to equal three; the final squared norm is proved to equal `1920682/7096546081`; consequently the actual squared amplification is `1920682/21289638243`. These facts also exclude a zero initial Euclidean norm. The general square/division identities used later are valid without adding a denominator hypothesis, so no unstated division side condition is hidden in the square-root bridge.

`witness_posDef` applies the existing diagonal positive-definiteness theorem to the three strictly positive diagonal values. `complement_diagonal` proves the actual identity matrix minus the witness equals `diag(9/10,1/2,2/5)`, after which the same library theorem proves complement positive definiteness. Matrix nonzeroness is witnessed by the `(0,0)` entry. The actual `spectrum_diagonal` theorem gives the spectrum, and checking the three exact values proves that one is absent. These are proved matrix properties, not assumed spectral certificates.

## True eigenvalue maximum

The central `actual_pairMaximum` proof was examined in both directions; it does not merely evaluate one selected pair or a proposed substitute list.

For the upper bound, `eigenvalue_in_witness_range` uses `hM.eigenvalues_mem_spectrum_real` and the exact witness spectrum. Thus each member of the actual eigenvalue list equals one of the three diagonal entries. `explicit_pair_bound` checks all nine ordered pairs of those values, including repeated values, and `Finset.sup_le` bounds every term in the actual distinct-index pair set by `1/121`.

For attainment, the proof places `1/10` and `3/5` in the actual spectrum, uses `hM.spectrum_real_eq_range_eigenvalues` to obtain actual eigenvalue indices realizing each, and proves those indices distinct by their unequal numerical values. Their term is exactly `1/121`. Membership in the actual pair set and `Finset.le_sup` give the reverse inequality. The final coercion simply unfolds the local pair set and function in the frozen definition. No choice of a computable eigenvalue ordering, permutation of a guessed list, or omitted multiplicity is needed.

The relevant pinned Mathlib source was inspected directly: `LinearAlgebra/Eigenspace/Matrix.lean` derives the diagonal spectrum from genuine eigenvalues of its matrix linear map, while `Analysis/Matrix/Spectrum.lean` derives eigenvalue membership and full spectral range from the spectral theorem. This validates the semantic bridge used by the proof.

## Correct second square and universal negation

`squaredNorm_nonneg` proves nonnegativity by a finite sum of squares. `euclideanNorm_sq` applies `Real.sq_sqrt`, and `actual_amplification_sq` derives the square of the actual norm quotient. `strict_scalar_gap` uses LeanCert in explicit kernel mode to prove

`1/14641 < 1920682/21289638243`.

This is the correct comparison: the proposed **unsquared** norm factor is already `Λ=1/121`, so its square is `Λ²=1/14641`. `strict_amplification_gap` proves nonnegativity of the actual quotient, applies the inspected `sq_lt_sq₀` equivalence for nonnegative quantities, and rewrites `(1/121)²=1/14641`. It therefore proves the required strict **unsquared** inequality without approximating any square root. The LeanCert certificate is used transitively by the exported counterexample and universal negation.

`not_isGreatest` puts the actual amplification at the proved nonzero initial vector into `amplificationSet`. Its strict excess contradicts the upper-bound component of an alleged greatest element. `not_fourStepConjecture_proved` instantiates the full original statement at dimension three with all required hypotheses proved. The separate positive-definite parameter family, semidefinite example, and asymptotic convergence question are not formalized or claimed by these exports; a single admissible strict violation settles this canonical universal identity negatively.

An independent exact-rational reconstruction using generic full matrix-vector multiplication, two executions of the map, and all nine ordered value pairs confirmed every coefficient, vector, denominator, and bound. The [reconstruction record](../verification/referee-2/exact-reconstruction.json) gives the exact values and the positive gap `6831066919/311701593515763`. The corresponding integer comparison is `1920682*14641=28120705162 > 21289638243`. This auxiliary computation is not used as a Lean assumption.

## Independent re-elaboration and trust

The reviewer independently ran `lake build Solution`, `lake env lean NLA/IE18/Proof.lean`, and `lake env lean Solution.lean`; all returned exit zero with Lean 4.33.1. The graph build reports 3683 jobs and reuses existing dependency artifacts. Actual Proof source re-elaboration took approximately 26 seconds in this run. Exact commands, environment, exit codes, timings, and log hashes are in [the check record](../verification/referee-2/checks.json).

The [Proof log](../verification/referee-2/reelaborate-proof.log) and [Solution log](../verification/referee-2/reelaborate-solution.log) report exactly `[propext, Classical.choice, Quot.sound]` for the five audited internal declarations (`strict_scalar_gap`, `residual_certificate_proved`, `actual_pairMaximum`, `counterexample_proved`, `not_fourStepConjecture_proved`) and all three public exports (`residual_certificate`, `counterexample`, `not_fourStepConjecture`). Every corresponding `#assert_trust kernel` passes. There is no sorry, admit, custom axiom, native evaluation tactic, unsafe declaration, local typeclass override, external implementation, or custom elaborator in the mathematical implementation. Challenge is not imported by the solution dependency chain, so its deliberate placeholders do not enter these proofs.

All ten dependency checkouts match their locked revisions and have no tracked modifications; see [the dependency audit](../verification/referee-2/dependencies.json). Input hashes remained unchanged after re-elaboration. These are independently observed local source/build results, not a claim to have rebuilt every dependency from scratch or run the authoritative Linux sandbox and Comparator.

## Reuse, proof quality, scope, and publication

The review applies the relevant [Tau Ceti rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics) to this one-problem NLA project. It does not impose Tau Ceti's unrelated roadmap or alter permanent NLA identifiers. The proof reuses existing diagonal matrix, spectrum, Hermitian eigenvalue, finite supremum, square-root, order, and rational-normalization APIs. Targeted searches found no existing library theorem replacing this residual counterexample or its actual pair maximum. The small wrapper facts isolate the custom norm and residual definitions; Solution's three wrappers deliberately expose the frozen Comparator target declarations. They are not an alternative conjecture or a compatibility layer.

The implementation is appropriately economical: exact diagonal algebra, nine scalar pair bounds, a noncomputational spectral range argument, and one scalar LeanCert check. It does not compute a chosen eigenbasis or eigenvalue ordering, optimize over a sphere, approximate eigenvalues or square roots, or subdivide an interval. The longer maximum proof is divided into upper-bound, attainment, and coercion steps. The single `change` at its end exposes the explicitly defined local pair set and term function and does not conceal a mathematical identification.

The code and numerical plan credit Matthew J. Colbrook for the counterexample and George Stepaniants for formalization, with the Department of Computing and Mathematical Sciences, California Institute of Technology, and an Apache license. The plan and review record disclose AI assistance and distinguish agent review from human review. No email for George Stepaniants is present in the formalization source inspected. The statement-first plan is explicitly dated and its historical future-tense wording is not a current formal verification claim.

The publication files arrived after the mathematical review and were subsequently reviewed independently as recorded below. No mathematical or transitive-trust issue remains on the hashes above; source changes must reopen the affected verification gates. The actual per-project Linux Comparator result remains pending.

## Publication addendum

The reviewer subsequently read the project README, actual v0.4 `formalization.yaml`, Comparator configuration, and root's independent proof-referee-1 report. The README accurately states the full negative result, both actual residual evaluations, the true eigenvalue maximum, the essential second square, and both positive-definiteness conclusions. It describes the actual local build and eight transitive-trust checks while explicitly retaining `Solved` and pending authoritative Linux verification. It does not claim the stronger parameter-family or asymptotic result is formalized.

The metadata correctly distinguishes Matthew J. Colbrook's informal mathematical proof from George Stepaniants's formalization. It includes the approved Department of Computing and Mathematical Sciences, California Institute of Technology affiliation, AI assistance, and accurately identified independent agent roles; it adds no email or human-review/source-author endorsement claim. Zero proof sorries are explicitly distinguished from the three isolated Challenge placeholders. All mathematical source hashes were rechecked unchanged.

The manifest lists exactly `NLA.IE18.residual_certificate`, `NLA.IE18.counterexample`, and `NLA.IE18.not_fourStepConjecture`. `comparator.json` requests those same three declarations, no definition holes, and only `propext`, `Classical.choice`, and `Quot.sound`. The actual shared validator reports `Manifest schema and comparator coverage: PASS (3 declarations)`. That configuration/schema check does not replace running Comparator on the committed project.

| Publication file | SHA-256 |
| --- | --- |
| `README.md` | `92a7ce11606e51e85383c131bb8db2a0f457666f3c93ad080f5c7379204914b2` |
| `formalization.yaml` | `c82f5ec204b515447f7b8b1b46899747e8139c6f8cebcb4e4ca5fcaab6ecadf4` |
| `comparator.json` | `7fd64ea1eb36dd9d29ae5888b0aeeb39fb96bd4bc12db7712cb6347098fcc1b6` |

The same values are retained in [the publication input record](../verification/referee-2/publication-inputs.sha256.json). These files are approved at these hashes with their truthful pending-Linux status. The successful shared checker-infrastructure selftest is not substituted for this project's still-required mathematical Comparator run.
