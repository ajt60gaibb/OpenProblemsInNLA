# TR-15 independent final proof review — referee 1

**APPROVE the complete seven-export mathematical proof.** No mathematical correction is requested. One documentation correction is required at the packaging stage: the current project README still says that no implementation exists. Actual Linux Comparator/default-kernel verification and the second independent final review remain separate gates; this report does not promote canonical status.

Reviewer: OpenAI Codex agent `/root/formal_review_standards`, 12 September 2026, independent of author `/root/leancert_examples`. I did not author or change these TR-15 statements or proofs. I read the complete canonical statement and Colbrook manuscript, all definitions and proof bodies, both frozen statement approvals, the numerical specification and correspondence, and the actual relevant Mathlib and LeanCert implementations. I independently reconstructed the small exact arithmetic and re-elaborated the candidate sources in a new artifact prefix. This is an independent agent review, not human peer review or Tau Ceti endorsement.

## Hash-bound scope

The proof freeze `1263937a8aeef77192d2eaf434457c36abefc77a7aefbd25fdf0dbd854ed7f6c` binds **75 project files and six canonical/manuscript files**. All 81 were checked before and after this review and remain unchanged. The six original sources also match their Git blobs at `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. Both independent statement approvals preceded implementation, as recorded by the retained gate.

| Frozen boundary | SHA256 |
| --- | --- |
| `NLA/TR15/Definitions.lean` | `63b8767fd19148b269f6e4041d464f0de5dc64cac82e1448fee43115bed55379` |
| `Challenge.lean` | `6778940f8f0f645fc6be0c57f1fb8f67791e0c67c896074651bca9cada491428` |
| `NUMERICAL_TARGETS.md` | `6851bb94fb8f6049980113b4df9a1346bd3ed9549f66dd74b2b1f6a5ee947cd6` |
| `NLA/TR15/Proof.lean` | `795f3b1305dfae77fe71ec1927b7d72e9d913a2ffd0475879880f33e55c959be` |
| `Solution.lean` | `dc31d2a6a1ef891bbdc9b6781a7a250c6751d539b7cd95c4a59d08638a8faeb1` |
| `comparator.json` | `80d0148e7ddf0a431d6833c3e464cf15424c94767394dd1a0fe93366c8bbb45f` |

## Full target and actual tensor semantics

The final theorem negates the complete original implication over every odd `m ≥ 3`, every `q ≥ 2` and `n ≥ 2`, and every real generator of length `qm(n−1)+1`. There is no even-q restriction, associated-matrix positivity, strong-Hankel condition, eigenpair-existence premise, or restriction to the selected witness in the universal target. Both tensors use the same generator with the exact prescribed orders and dimensions.

The finite array model is faithful: each entry is the actual generator at the sum of zero-based indices; the length bound is proved, with no default entry. The lower tensor's cast identifies equal finite lengths without changing values. The contraction sums over every ordered tuple and multiplies one signed real coordinate per slot. Its natural-number exponent is exactly `s−1`. The eigenvector is required to be nonzero, and every component equation is present. The total definitions at order zero do not enlarge the admissible domain. The source uses multi-way arrays, these generator conventions and componentwise-power H-eigenpairs, and states the same inheritance conjecture in final Section 4. I independently checked PDF pages 2, 3 and 21 of the [Ding–Qi–Wei primary paper](https://www.polyu.edu.hk/ama/staff/new/qilq/BIT-DQW.pdf).

The elaborated environment confirms these definitions and all seven exported signatures. The complete normalized Challenge and Solution signatures are identical and exactly match the Comparator list. This local signature check supplements semantic review; it is not presented as the later independent-environment Linux Comparator result.

## Proof audit

`lower_contractions` genuinely reindexes the full ordered-pair sum with `finTwoArrowEquiv`, `Fintype.sum_equiv` and `Fintype.sum_prod_type`, then proves all three components for an arbitrary real vector. Independently enumerating all 27 one-based source entries reproduces the same polynomials. In particular, the first component is `(x₀+x₂)²+x₀²+x₁²+x₂²`.

The strict-positivity helper is valid for every nonzero real vector: if this sum were nonpositive, nonnegativity of all four squares would force all three coordinates to vanish. For an arbitrary actual H-eigenpair, the first equation sets this positive expression equal to `λx₀²`. The proof excludes `λ ≤ 0` directly, without dividing by a possibly zero coordinate or computing a spectrum. Thus `lower_eigenvalues_pos` proves the full universal premise, rather than a property of one selected pair.

The optional `lower_eigenpair_exists` theorem genuinely proves nonvacuity. Its real polynomial is continuous; exact evaluation gives endpoint values −1 and 2. The actual `intermediate_value_Ioo` conclusion supplies a root strictly in `(0,1)`. The proof then checks the three genuine contraction equations at `(1,0,t)` and `λ=2+2t+2t²`, and proves nonzero by the first coordinate. My separate exact reconstruction produces third-equation residual `2t⁴+2t³+3t²−4t−1`, with the required endpoint signs. No root approximation or root-existence assumption is introduced.

For `upper_contraction`, the finite-product zero lemma shows that any tuple other than the all-one tuple contributes zero. `Finset.sum_eq_single` retains exactly one term per component, at generator indices 5 and 6. This proves the actual contraction `(0,−1)` at `(0,1)`. My independent 64-entry source calculation agrees. `upper_negative_eigenpair` proves nonzero and all coordinatewise fifth-power equations. `counterexample` establishes all original parameter restrictions and combines universal lower positivity with failure of the upper conclusion. `not_inheritanceConjecture` applies the complete quantified statement to this exact shared-generator instance. There is no weakened intermediate target substituted for the original conjecture.

## Fresh checks, retained certificate and trust

My new driver freshly compiled Definitions, Proof, Solution, the isolated Challenge, and a separately written environment inspection. All five commands exited zero. Only Challenge emitted its seven intentional placeholders; Proof and Solution never import Challenge. The old project build path was excluded from `LEAN_PATH`. A sixth inspection then audited the actual Boolean-checker equality used inside the LeanCert term. It also exited zero without warnings.

All **15 candidate `#assert_trust kernel` commands and corresponding axiom reports** passed with exactly `propext`, `Classical.choice`, and `Quot.sound`. My additional traversal audits both types and proof bodies of all **46 reached project declarations**, including private helpers and definitions, and rejects every other transitive axiom. It also verifies the actual presence of 14 substantive dependencies, including finite-sum reindexing, the real open-interval IVT, and the checked LeanCert theorem. There is no custom axiom, `sorryAx`, native-compiler trust or Challenge dependency in the proof closure.

The LeanCert certificate uses the constant negative-one expression on the singleton interval `[0,0]`, upper bound zero, precision −53 and depth 10. The term calls `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`. Crucially, I separately inspected its actual Boolean-checker helper, not merely the precision inequality: `checkStrictUpperBoundDyadicChecked … = true` is proved by `of_decide_eq_true (id (Eq.refl true))` and passes its own kernel-trust check. The certificate supplies the strict-negativity field of the negative eigenpair theorem, which is consumed by the counterexample and final negation. It is not an unused certificate. No interval subdivision, tensor eigenvalue enumeration or numerical root isolation is performed.

All ten dependency repositories are clean and match the frozen manifest, including Lean **4.33.1**, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. These checks ran on macOS arm64 using matching compiled dependency artifacts. They do not claim a fresh source rebuild of every dependency, Linux isolation, Comparator execution or an external human review.

## Review standards, documentation finding and next gate

I applied the relevant [Tau Ceti rubrics at the campaign's pinned revision](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics): semantic fidelity and nonvacuity, proof quality, reuse, scope, generality, API, placement, naming, documentation and attribution. This is one coherent canonical target, with appropriate finite-array definitions and short mathematical helpers. The searched pinned Mathlib tree has no direct Hankel H-eigenpair development replacing these definitions; existing finite-sum and IVT APIs are substantively reused. The named Solution wrappers serve the required frozen Comparator boundary, rather than an obsolete compatibility layer. A new general tensor-product or spectral solver interface would add unnecessary work. Tau Ceti-specific namespace and roadmap rules are adapted to this repository's `NLA.TR15` layout and canonical target.

**Documentation finding D1 — required before publication:** `lean/README.md` still states “It has no proof implementation” and describes writing Proof/Solution as future work. This is stale at the completed-proof stage. Refresh its present-tense status and evidence links during the already-planned metadata preparation, preserving the historical freeze record and accurately keeping Linux verification pending until it passes. No mathematical source or frozen Challenge change is needed. The completed-proof report is accurate. This finding does not invalidate the mathematical approval above.

Mathematical authorship remains Matthew J. Colbrook's. George Stepaniants is credited for formalization, with the Department of Computing and Mathematical Sciences, California Institute of Technology affiliation and AI assistance. No George email, authorship transfer, historical priority or human endorsement is claimed. The proof does not establish a classification of all odd-order tensors or refute results with an additional positive-semidefinite associated Hankel matrix hypothesis.

The independent [evidence manifest](proof-referee-1-evidence/evidence-manifest.json), SHA256 `0c70ddac444ef31253cdaedc8dc55d9954d5eabf1e0683b3c0d1449b95f5725a`, binds 25 review files, including reproducible drivers, full commands, raw logs, pin/source checks, exact reconstruction and read-library/rubric hashes. The actual-environment inspection is `0d8c85a1eccd0e381de304e549706f42c227b9f15bbfed3dfdc32e18a4d3d5e5`; the separate Boolean-checker log is `389c94fe7e3fd6ddd71ac390ef75e8ad3bee09767248fc451fa8fddeea4e12ae`. The fresh command record is `2a28ca614bd459240d7adba43d9444b8c558b3c0d698f1af1e99b8ea53b5b7b5`.

No candidate source, canonical status, ID, commit, push or pull request was changed by this referee. The next gates are the second independent final approval, truthful packaging including D1, and actual Linux verification with the repository's full controls.
