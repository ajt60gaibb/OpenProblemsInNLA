# Independent proof referee 1 — IE-19

**Verdict: PASS for the complete negative formalization of the original IE-19 target at the exact source hashes below.** No mathematical or proof-quality correction is requested. **Linux Comparator/replay and final publication evidence remain pending release gates**; this report does not assert those checks have run or authorize a premature catalog promotion.

Reviewed on 2026-09-12T15:16:01+00:00. Reviewer: Codex agent `/root/solved_statement_inventory`. I did not author or edit the IE-19 definitions or proof. I previously reviewed its statement boundary; this review now inspects the completed proof and exports independently. This is automated-agent review, not external human peer review.

## Reviewed sources and repeat checks

The original canonical target and Colbrook manuscript Section 1 were read from upstream `5adea969c17391693978ada2674d25bb5c3daeb1`. I reread the full current `Definitions.lean`, `Proof.lean`, `Challenge.lean`, numerical targets and `Solution.lean`. The statement hashes still equal those approved in my earlier statement-referee report, and the proof/export hashes match the root's successful build record.

I inspected `verification/proof-build.log`, `verification/proof-build.json`, and `verification/axioms.log`. Then I independently ran both commands below, each exiting **0**:

```sh
lake env lean NLA/IE19/Proof.lean
lake env lean Solution.lean
```

The first command re-elaborated the entire proof source, including the explicit kernel-mode LeanCert certificate and internal trust assertions. The second checked the public exports and their trust assertions. This is stronger than merely reading a cached successful Lake build message; it remains a local Lean check, not the separate Linux Comparator or independent-kernel replay. The exact output is preserved in `proof-referee-1-replay.log` and `proof-referee-1-exports.log` beside this report.

Both reruns reported only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` for every requested declaration. No `sorryAx`, custom axiom, or native-execution trust appears. The corresponding `#assert_trust kernel` commands succeeded. `Proof.lean` imports `Definitions` and `LeanCert.Tactic`; `Solution.lean` imports `Proof`. Neither imports the Challenge module containing deliberate comparison-environment placeholders.

## Mathematical and dependency audit

1. **The original problem is exercised nonvacuously.** The original universal parameters n≥3, m>0, α≥(n−2)m and the exact entrywise, symmetric, weak-dominance matrix class are retained. The proof constructs the admissible point n=3, α=m=1 rather than assuming an inaccessible abstract structure. The counterexample therefore applies inside the original class.

2. **Every admissibility condition is proved.** Finite case splits establish transpose symmetry and all nine strictly positive entry bounds. The dominance argument establishes full row sum 3 and diagonal 2, then uses mathlib's erased-sum identity to conclude the off-diagonal sum is 1≤2. No Loewner order or strengthened diagonal-dominance premise has replaced the original condition.

3. **The inverse is the true inverse.** Both explicit matrix products are checked entry by entry as right-inverse identities. The proof uses `Matrix.isUnit_det_of_right_inverse` and `Matrix.inv_eq_right_inv` to establish determinant invertibility and identify the standard matrix inverse. It does not evaluate a totalized inverse at a singular input. I independently checked the underlying arithmetic: J has diagonal 2/off-diagonal 1/2; its inverse has diagonal 5/9/off-diagonal −1/9. The comparison inverse has diagonal 3/4/off-diagonal −1/4.

4. **The norm is the requested one.** The finite supremum of nonnegative absolute row sums is evaluated after proving all three row sums equal the respective rational constant. `Finset.sup_const` uses the genuine nonempty row-index set. Consequently the outputs are exactly 7/9 and 5/4 in the induced row-sum infinity norm; an entrywise maximum or a bound for only one row would not justify these theorems and is not what this code proves.

5. **The numerical certificate has the right role.** Exact finite algebra proves the matrix products, inverse identities, row sums, and comparison expression. `strict_scalar_gap` uses `leancert (trust := kernel)` for 7/9<5/4. The assembled witness uses this theorem, rather than trusting a Python result or silently leaving the analytic reduction as an assumption. The small point comparison requires no interval subdivision or spectral approximation.

6. **The public result negates the whole canonical claim.** `not_lowerBoundConjecture_proved` instantiates all original scalar assumptions at the concrete witness and contradicts its asserted weak lower bound with the proved strict reverse inequality. `not_sharpConjecture_proved` extracts the inequality conjunct from the original equality-characterized conjecture and uses that contradiction. The conclusion is a full negative resolution of the original yes/no target. The later all-parameter sharp-infimum replacement and its nonattainment are additional source results, expressly unclaimed by this formalization.

## Tau Ceti rubric application

I read the published correctness, scope, proof-quality, reuse and attribution rubrics in the pinned TauCetiReview source `afb424eda89e8ac96d9eb69f6a88972055a4cd1b` and applied them to this repository's stated formalization objective. This is an independent agent review using those rubrics, not a claimed run or endorsement of the Tau Ceti review service.

| Rubric | Assessment |
| --- | --- |
| Correctness and faithfulness | PASS. I checked for vacuous quantifiers, hidden numerical hypotheses, totalized-inverse artifacts, wrong norms, and reversal of implications; the concrete proofs exclude these failures. |
| Scope | PASS for this project. One coherent contribution formalizes one already solved canonical problem. No unrelated refactor or unproved stronger replacement is bundled. Tau Ceti's separate roadmap repository is not the governing roadmap for OpenProblemsInNLA. |
| Proof quality | PASS. The script uses short named stages, finite case checks, `norm_num`, `linarith`, and direct library inverse/supremum lemmas. There is no long opaque tactic script, undocumented `change` maneuver, giant interval computation or unsafe evaluation. |
| Reuse | PASS with the statement-boundary adaptation explained below. The proof reuses mathlib inversion and finite-sum/supremum APIs instead of rebuilding matrix analysis. |
| Attribution | PASS. The code and numerical-target document identify Colbrook's mathematical counterexample, George's formalization authorship and approved Caltech department/university affiliation. No new mathematical priority or human-review claim is made, and George's email is absent. |

For reuse, I searched the pinned mathlib source. The located APIs are `Matrix.isUnit_det_of_right_inverse`, `Matrix.inv_eq_right_inv`, `Finset.sum_erase_add`, and `Finset.sup_const`, all used directly. Mathlib's `Matrix.linfty_opNorm_def` and `Matrix.linfty_opNNNorm_def` describe the same row-sum norm under a different norm-instance scope. The explicit `rowSumNorm` definition is a proof-independent, norm-instance-stable comparison boundary, not a new parallel theory of operator norms; the implementation does not reprove generic norm results. Likewise, the short `Solution` exports serve the deliberately separate Comparator environments, not a compatibility shim or duplicate library API. Those project-specific necessities justify adapting the rubric's general discouragement of thin aliases.

## Remaining release evidence

- Run the configured Linux Comparator against the isolated Challenge and Solution environments and record the exact successful declaration comparisons and independent replay scope. This review does not substitute for it.
- Bind the proof source, toolchain and dependencies to immutable publication revisions; include the required formalization metadata, CI/reproduction commands and dated logs.
- Preserve the reviewed statement and proof hashes or re-review subsequent substantive changes. A source change cannot inherit this exact-byte verdict automatically.

## Hash binding

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `NLA/IE19/Definitions.lean` | 3019 | `32dc631cd600154948963a875559cd610d974764fc77f13ab242a573c6dd22b3` |
| `Challenge.lean` | 669 | `c79e602bde37c5395eda1376635054776c72c1d803737e1dbfe0a963899627bb` |
| `NUMERICAL_TARGETS.md` | 3893 | `71bab6295627b5d68e63a41bfae8a5e82ce11900d334846636f85cf454814c24` |
| `NLA/IE19/Proof.lean` | 5363 | `06a534c417911f7db8aca8310699c3862eaf535f8b34ec20b5551218c20a5460` |
| `Solution.lean` | 1033 | `72fa6092d37c32eb453af0ba83974cc541cb15730080c96dfbaa9226a6f6f658` |
| `lakefile.toml` | 280 | `10d0c9c9dc8b8ac29e372807b94ca53b644aa5c032e6c4b7eb32c90736be66ef` |
| `lean-toolchain` | 25 | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lake-manifest.json` | 3884 | `0b2982e346ad245431120cb2eeafa466c9336f1e8bf11525312c0982cb840cb3` |
| `verification/proof-build.log` | 981 | `0563829a984c66d94330be5f16b7d14c094580181a2f8105aad01b2f2803aca0` |
| `verification/axioms.log` | 859 | `435f2501cbb2c153762f8d2b57ec5e229ac93a16e6463d97f5998ecb3bc38ddd` |
| `reviews/proof-referee-1-replay.log` | 379 | `ac245ba50bb03310248aace6e1850189198ca29b15cb49f125150a92b9636848` |
| `reviews/proof-referee-1-exports.log` | 270 | `f5fb8782755aa1029d41b0159bebfa38c18cc1d80f6d71c8cd6631a5d67c789f` |

Canonical README SHA-256: `eea3c53d86f17e4e41a9d1ebcf62454ebd1ac0c296b9305137e44a47bf283488`. Colbrook source manuscript SHA-256: `4c50113b3ca261779be36a0058e6b79cb594225098268cd8cc815e6b87b905a4`.
