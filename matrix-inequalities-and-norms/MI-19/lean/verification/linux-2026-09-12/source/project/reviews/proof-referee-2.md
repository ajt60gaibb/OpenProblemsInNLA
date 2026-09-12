# MI-19 independent proof referee 2

**Verdict: approve the completed mathematical implementation on the hashes below.** The full canonical conjecture is refuted by a proved admissible complex positive-semidefinite witness and a strict inequality between real-valued permutation sums. No mathematical correction is requested. Authoritative Linux Comparator verification and the final publication metadata remain pending; this review alone does not authorize a Lean-verified catalog status.

Reviewer: independent Codex agent `/root/formal_review_standards`, 12 September 2026. The reviewer did not author the MI-19 definitions, statements, proof, or solution wrapper, and did not change them during this review. This is AI-agent review, not human peer review or an official Tau Ceti service verdict.

## Bound inputs and evidence

The complete original canonical README, full Colbrook `solution.tex`, attribution/scope note, frozen numerical plan, both prior statement reviews, Definitions, Challenge, Proof, and Solution were read. The canonical README and complete manuscript were independently compared byte-for-byte with upstream commit `5adea969c17391693978ada2674d25bb5c3daeb1` and match it.

| Input | SHA-256 |
| --- | --- |
| `NLA/MI19/Definitions.lean` | `170e406d1f6bf0ca60e5b65998308b030cf08cc0def51c25c9860524ad3441ac` |
| `Challenge.lean` | `9c838a34cbff20eceb5e842eeca77c310bccb442843925343a7827a1020063cb` |
| `NUMERICAL_TARGETS.md` | `cd93a4cefb529b69755c10bae600718442e0e6b8749c37df87c6dabec9b751aa` |
| `NLA/MI19/Proof.lean` | `53ab38bfef6e52f6c039eba5056659be43f9b8e7a7b3453a62769dc3f0ef3c37` |
| `Solution.lean` | `18bf53ea1d745b4488718297559c3c77e3bcb902596b9c9aae5f448bdcb800c4` |
| Canonical MI-19 README | `6102736589b7b36c1dd3579cb48cfba58ec07ac708c4ce0b9c50409e6172b77b` |
| Full Colbrook `solution.tex` | `5d7278870da8bde55b87f77539e389ebb1dcc6debf3d1a588a00d7710e41ea0c` |

The [complete input record](../verification/referee-2/inputs.sha256.json) also binds the toolchain, Lake configuration, dependency manifest, license, and attribution note. All three mathematical statement files retain the hashes approved before proof implementation. Both public Solution theorem signatures match their Challenge signatures literally after whitespace normalization; this direct source check is recorded in [statement identity evidence](../verification/referee-2/statement-identity.json). It is supplementary to the pending Comparator check, not a substitute for its isolated environment comparison and replay.

## Correctness and original-target fidelity

The audit applied [Tau Ceti correctness and faithfulness](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/correctness.md) adversarially to every new definition and both exported claims. No weakened quantifier, vacuous premise, assumed numerical certificate, changed index ordering, wrong field, or inequality reversal was found.

`SubsetConjecture` preserves every original hypothesis and quantifier: every `n≥2`, every complex Hermitian positive-semidefinite matrix, every real `q∈[0,1]`, and every nonempty proper subset of the ordered index type. It is not restricted to real entries, diagonal matrices, initial segments, singletons, positive-definite matrices, or entrywise nonnegative matrices. A real matrix embedded in the complex matrices is a legitimate witness against this full domain.

The actual pinned Mathlib `Matrix.PosSemidef` definition requires Hermitian symmetry and nonnegative star-quadratic forms on all finitely supported complex vectors; its finite-dimensional characterization quantifies over all complex coordinate vectors. The proof establishes all sixteen entries of `gramFactor.conjTranspose * gramFactor = witness` using exact matrix multiplication, then invokes `Matrix.posSemidef_conjTranspose_mul_self`. The inspected library theorem derives nonnegativity from a sum of terms `star z * z`. Thus the argument proves genuine complex PSD, not merely positivity on real test vectors or a numerical eigenvalue approximation. Hermitian symmetry is derived from the resulting PSD proof.

`inversionCount` counts precisely the increasing index pairs whose images reverse order. It examines the full `Fin n` ordering and uses a natural-number exponent, retaining `0^0=1`. Every `qPermanentTerm` uses all matrix entries `A i (σ i)` and the exact real weight embedded in the complex field. The restricted sum filters the same full permutation type by `S.image σ = S` and reuses the identical term function. It does not reorder or renumber either block and does not replace the subset sum by a product of two smaller q-permanents. The chosen Lean singleton `{1}` is paper index `{2}`, an interior position. Setwise preservation specializes correctly to fixation of that one position.

The complete universal statement uses Mathlib's scoped partial complex order, inspected in `Analysis/Complex/Order.lean`: it compares real parts and requires equal imaginary parts. Both concrete sums are proved to have imaginary part zero, and the strict inequality is obtained from a strictly negative real difference embedded in the complex field. No incomparability artifact is involved. For the general Hermitian domain, conjugating a term pairs it with its inverse-permutation term; inversions agree under inverse and the preserving permutations are closed under inverse. This mathematical fidelity check explains why the formal order agrees with the intended real-valued inequality without adding a reality premise to the conjecture. The formal counterexample itself establishes its two reality facts explicitly.

The source's rank-two assertion and positive-definite perturbation extension are correctly excluded from the formalized claims. They are not necessary to refute the exact universal PSD target. The separate MI-18 monotonicity question is not claimed resolved by this proof.

## Proof and enumeration audit

The argument connects every scalar computation to the actual matrix and actual permutation sums:

1. `gramFactor_mul` proves the exact Gram identity, and `witness_posSemidef` derives PSD from it.
2. `sum_perm_succ` uses the existing Mathlib equivalence `Equiv.Perm.decomposeFin` and `Finset.univ_perm_fin_succ`. Their actual implementations were inspected: the finite permutation universe is the bijective image of a position and a permutation on one fewer position. Recursive expansion therefore covers all `4!=24` permutations once; it is not an externally supplied list whose completeness is assumed.
3. `inversionCount_fin4` is proved from the original filter-cardinality definition by summing over all index pairs. Its six remaining tests are exactly the six increasing pairs in order four.
4. `qPermanent_witness` evaluates the resulting complete sum at `q=7/8`. `restrictedQPermanent_witness` expands the actual filter by setwise preservation before evaluating its terms. It retains precisely the six permutations fixing the interior index, with their original full-order inversion counts.
5. The two exact complex evaluations give their imaginary parts and their difference. The scalar fact `(-3235575:ℝ)/16384 < 0` is proved by `leancert (trust := kernel)` and is used by `strict_counterexample`, so LeanCert contributes to the exported result rather than merely proving an unused test.
6. `Complex.real_lt_real` and the exact gap identity transfer the scalar certificate to a negative complex difference. Translation invariance of the order then supplies the strict reverse inequality. `counterexample_proved` establishes all admissibility facts as conclusions. `not_subsetConjecture_proved` instantiates the full universal statement at dimension four and contradicts its reverse weak inequality.

As an independent auxiliary check, the reviewer reconstructed all sixteen Gram entries and enumerated all 24 permutations using only Python `itertools.permutations`, exact `fractions.Fraction` arithmetic, and an explicit set-image test. No supplied checker or Lean enumeration table was imported. The [full reconstruction record](../verification/referee-2/exact-reconstruction.json) includes every permutation, inversion count, entry product, selected-subset flag, and rational term. Exactly six permutations preserve the singleton. The resulting full sum is `335001935775/16384`, the restricted sum is `167502585675/8192`, and their difference is exactly `-3235575/16384`. Both polynomial coefficient lists also agree with the entire informal manuscript. This finite auxiliary reconstruction supplements, and is not an assumption of, the Lean proof.

## Independent build and transitive trust

The reviewer ran all of the following independently on macOS with Lean 4.33.1:

- `lake build Solution`: exit 0; the build graph contains 3640 jobs, with existing dependency artifacts reused.
- `lake env lean NLA/MI19/Proof.lean`: exit 0; actual proof source re-elaboration, approximately 23 seconds in this run.
- `lake env lean Solution.lean`: exit 0; actual solution source re-elaboration.

The [command record](../verification/referee-2/checks.json) gives exact commands, exit codes, environment, elapsed times, and hashes of the raw logs. The actual [proof output](../verification/referee-2/reelaborate-proof.log) and [solution output](../verification/referee-2/reelaborate-solution.log) report exactly `[propext, Classical.choice, Quot.sound]` for all five audited internal declarations and both public exports:

`qPermanent_witness`, `restrictedQPermanent_witness`, `strict_scalar_gap`, `counterexample_proved`, `not_subsetConjecture_proved`, `counterexample`, and `not_subsetConjecture`.

Every corresponding `#assert_trust kernel` completed successfully. The pinned LeanCert trust implementation was inspected: it collects transitive axioms, accepts those three foundational axioms, and rejects sorry, native/compiler, and custom dependencies in kernel mode. There is no `sorry`, `admit`, custom `axiom`, native evaluation tactic, unsafe declaration, external implementation, local instance override, or custom elaborator in the mathematical implementation. Ordinary `decide` is used only for finite subset properness and leaves no additional axiom. Challenge is not imported by Definitions, Proof, or Solution; its two deliberate target placeholders do not occur in the solution's dependency closure.

All ten checked-out dependency revisions match the locked manifest and have no tracked modifications; see [the independent dependency record](../verification/referee-2/dependencies.json). Inputs were rehashed after re-elaboration and did not change. These are local build and source-review results. They do not claim a clean-room rebuild of all dependencies, a Linux sandbox result, or the still-pending authoritative Comparator run.

## Computation, reuse, API, documentation, and attribution

The review also applied the relevant [proof-quality](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/proof-quality.md), [reuse](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/reuse.md), [API](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/api-design.md), [documentation](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/documentation.md), [scope](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/scope.md), and [attribution](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/attribution.md) angles, adapted to this repository's self-contained, one-problem verification layout. Tau Ceti's own roadmap and compatibility policy are not imposed on permanent NLA problem identifiers or the required Comparator boundary.

The proof makes sensible use of the existing Gram, finite-permutation equivalence, finite-sum, complex-order, and rational-normalization APIs. Targeted searches in the pinned Mathlib and LeanCert sources found no existing q-permanent/subset counterexample API or theorem directly replacing the new mathematical development. The concrete index specializations are transparent applications of the existing permutation evaluation lemma, have real consumers in the exact reduction, and document why they exist. They introduce no unchecked enumeration or parallel permutation theory. The generic sum reduction and witness-specific steps remain in the `NLA.MI19` namespace. The Solution wrappers intentionally preserve the independently frozen public Challenge types for Comparator; they are not obsolete compatibility aliases.

Computations are minimized appropriately: a fixed 2×4 Gram factor, six inversion tests, 24 exact terms, and one scalar LeanCert inequality. No eigenvalue calculation, matrix-domain search, parameter interval, or interval subdivision is needed. The proof does not attempt to establish the larger polynomial identities when evaluating the one sufficient rational point gives the needed result directly. Lemmas separate admissibility, the two sums, the exact gap, order transfer, and universal negation; no large opaque certificate is accepted as an assumption.

The mathematical files and numerical plan identify the informal counterexample as Matthew J. Colbrook's and the formalization as George Stepaniants's. The supplied public affiliation is the Department of Computing and Mathematical Sciences, California Institute of Technology. AI assistance and the difference between agent review and human review are disclosed in the numerical plan and reviews. No email for George Stepaniants is present in the formalization source inspected. The Apache license is supplied. The historical statement-first wording in `NUMERICAL_TARGETS.md` is dated and is not mistaken for a current proof-status report.

The publication files arrived after the mathematical review and were subsequently reviewed independently as recorded below. The required authoritative Linux Comparator result remains pending.

No blocking mathematical, trust-closure, or statement-fidelity issue remains on the bound sources. Any change to these mathematical files requires rechecking the affected proof and statement gates before publication.

## Publication addendum

The reviewer subsequently read the project README, the actual v0.4 `formalization.yaml`, and `comparator.json`. The README accurately describes the complete negative target, the original inversion order and setwise-preserving restriction, the genuine complex PSD witness, actual local re-elaboration, standard-three axioms, and the pending authoritative Linux check. The optional exact rank, all-q polynomial identities, and positive-definite perturbation claims are expressly excluded. It credits Colbrook for the mathematical counterexample and Stepaniants for formalization with the approved department/university affiliation and no contact email.

The manifest honestly records agent review without human review or source-author endorsement and distinguishes zero sorries in the actual proof closure from the two isolated Challenge placeholders. Its two `main_results` match the exact public exports. The Comparator configuration requests those same two declarations, no definition holes, and only the standard three permitted axioms. The actual shared validator reports `Manifest schema and comparator coverage: PASS (2 declarations)`. This metadata check is not a proof certificate.

Publication hashes, also retained in [the publication input record](../verification/referee-2/publication-inputs.sha256.json):

| File | SHA-256 |
| --- | --- |
| `README.md` | `7a67af7ebea1963505c55ceb45156817367b0edcd67c6095b9a3d00c2eea7b2c` |
| `formalization.yaml` | `41a5bfd6fb0435e6161a14ae51631c1a72bf75ebe53600260369174df45b53cf` |
| `comparator.json` | `11fdab27c092b2f77486078bd40eb33b4ad439d6ca8e9ca38941b5882854b194` |

The publication files are approved at these hashes with their explicit pending-Linux status. No completed Comparator run or catalog promotion is claimed by this addendum.
