# RA-09 — Lean formalization of concave Frobenius error transfer

**The complete seventeen-export proof passed two independent mathematical reviews and actual Ubuntu Comparator/default-kernel verification.** The [canonical problem](../README.md) records its full original target as **Lean verified**. The checked immutable revision and retained evidence are documented below.

Mathematical theorem: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization: **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, with AI assistance. Persson, Meyer and Musco retain attribution for the original question. The formalization's Apache-2.0 license does not reassign the source manuscript.

For every n≥2, 1≤k<n, real symmetric PSD pair A≥Ahat≥0, continuous concave nondecreasing nonnegative half-line function f, every selected ordered orthonormal eigenbasis, and every epsilon≥0, the theorem proves

```math
\|A\|_F^2-\|\widehat A_k\|_F^2
\le (1+\varepsilon)\|A-A_k\|_F^2
\quad\Longrightarrow\quad
\|f(A)-f(\widehat A)_k\|_F^2
\le (1+\varepsilon)\|f(A)-f(A)_k\|_F^2.
```

Each matrix's ordinary and function truncations use the same selected eigenvectors, including arbitrary choices in repeated eigenspaces. The full function class includes f(0)>0. The premise remains the canonical difference of squared norms. Colbrook's ordered residual theorem supports this conclusion through the proved trace identity

```math
\|A-B\|_F^2=\|A\|_F^2-\|B\|_F^2-2\operatorname{tr}(B(A-B))
\le\|A\|_F^2-\|B\|_F^2,\qquad B=\widehat A_k.
```

[Definitions](NLA/RA09/Definitions.lean), the independently reviewed [Challenge](Challenge.lean), and [Solution](Solution.lean) give all **17 exact exports**, selected by [comparator.json](comparator.json) with no definition exceptions. [PROOF_MAP.md](PROOF_MAP.md) maps their complete proofs. Genuine Mathlib Frobenius norm, PSD order, spectral theorem and CFC are connected by proved semantic lemmas. Actual matrix overlap weights supply the harmonic and averaging bounds. Under the original premise, when the ordinary tail is zero, both function-error squares are (n−k)f(0)^2 for every allowed null-space basis. Selected zero columns and f(tau)=0 are also covered.

The proof uses exact unbounded scalar factorizations and a sum of squares, followed by finite matrix algebra. **LeanCert's actual kernel trust assertions** inspect the resulting theorem dependencies. No interval subdivision, numerical oracle or artificial point certificate is needed. Only propext, Classical.choice and Quot.sound are permitted; there are no proof admissions. Challenge's 17 intentional reference placeholders are kept outside the implementation import closure. The source's broader monotone-subhomogeneous class, unordered factor two, sharpness, complex extension and k=n endpoint theorem are outside these exports.

## Reviewed evidence

The [statement freeze](reviews/statement-freeze.json) binds 31 project inputs and 17 original source/policy files; two independent statement approvals preceded implementation. The [full proof freeze](verification/proof-freeze.json) binds 361 project inputs and the same originals. The [completion report](reviews/proof-completion.md), [referee 1](reviews/final-referee-1.md), and [referee 2](reviews/final-referee-2.md) retain exact hashes and complete evidence inventories.

All checks below were fresh **local macOS** compilations with private target prefixes and ten exact dependencies reused read-only. The author passed 18 direct commands and 49 kernel/standard-three reports. Referee 1 passed 18 commands and 66 reports, including 17 extra inspector reports; referee 2 passed 19 commands and 50 reports, including a literal actual-Frobenius-norm/CFC consumer. Both independently matched all 17 elaborated statements and inspected the actual proof path: 115 project declarations and 40 required material bridges for the final target, 139 and 49 for all exports. Their complete raw attempts are retained, including referee 1's corrected report-count parser and referee 2's corrected import-order diagnostic. Neither required a mathematical change.

Implementation/route contributors /root/leancert_examples, /root, /root/formal_review_standards and /root/solved_statement_inventory are ineligible as independent final referees. The final referees are /root/ra09_final_referee1 and /root/mf16_final_referee. The latter subsequently prepared candidate documents and conducted the operational audit; those roles add no mathematical approval. [Coordinator acceptance](verification/final-review-acceptance.json) binds both reports and their complete evidence. Actual non-root Ubuntu Comparator/default-kernel replay and rejection controls have passed, followed by independent operational review and coordinator acceptance. Publication review is the remaining gate.

The frozen OrderedExistence.lean header calls Colbrook's result a “counterexample”; this is a disclosed, nonblocking copied comment typo for the affirmative theorem. Frozen Lean bytes remain intact. The exact old README is [archived](verification/pre-candidate-README.md). NUMERICAL_TARGETS.md, SourceCorrespondence.md, PROOF_MAP.md and older handoffs retain their dated phase descriptions; the current status is stated here and in [formalization.yaml](formalization.yaml).

## Reproduction and pins

Lean is 4.33.1; Mathlib is 0df444a360eaa60ab8c11dca51a86af692955474 and LeanCert is 621a43d7cf21f87872392a01e874f2f1dbddc926. [lake-manifest.json](lake-manifest.json) pins all ten dependencies. With those dependencies installed, explicitly build the proof:

```sh
lake build Solution
```

The unchanged default target is Challenge. Reproduce the authoritative check on immutable candidate `3bcc863070c037fffb1deee3f12d1cd1517727df` using the repository's [Linux workflow](../../../.github/workflows/lean-verification.yml), [pinned verification instructions](../../../docs/lean/README.md), and the exact commands on the [canonical page](../README.md#lean-proof-and-verification-evidence---2026-09-13). Local builds are separate development checks.

The [source correspondence](SourceCorrespondence.md) credits the original manuscript, Mathlib construction and locally adapted RA-08 spectral design. Pinned examples are [Schiffer](https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1) and [Forsythe](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof). Review follows the repository's adaptation of [Tau Ceti](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics); metadata uses the pinned [v0.4 standard](https://github.com/mathlib-initiative/formalization.yaml/tree/99c678e569c7c4c0772db297c5ddd5e4c9b6322e). No external human review, official endorsement, current public-fork search or new mathematical priority is claimed.


## Actual Ubuntu verification and publication preservation

[Run 34738884548](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34738884548) verified immutable candidate `3bcc863070c037fffb1deee3f12d1cd1517727df`. All 17 jobs and every step passed. The actual RA-09 job ran on Ubuntu 24.04 x86_64 with Lean 4.33.1, the pinned Comparator/exporter and the strict sandbox as UID 1001. It freshly checked out all ten dependency revisions and used 8,690 matching official Mathlib cache objects. Challenge/Solution graph sizes were 2,710/2,726 jobs; this is not a claim to rebuild all dependencies from source.

Both actual export lists contain exactly the seventeen advertised declarations without definition exceptions. Default-kernel replay accepted Solution. All 49 embedded LeanCert kernel assertions and standard-three reports passed; the Solution build emitted no warnings or admissions. The final referees' 66 and 50 reports include their additional independent diagnostic checks and remain separately recorded.

The target and standalone checker jobs each ran the actual sandbox probes, three raw-kernel controls, five Comparator fixtures and actual admission/native rejection controls. Bad exported proofs were rejected for `sorryAx` and `checked._native.native_decide.ax_1_1`. The nested Bubblewrap executable was denied UID-map setup before its inner write ran; this is not an observed inner-write denial or a general sandbox-security proof.

The [independent operational report](verification/linux-2026-09-13/OPERATIONAL-REVIEW.md) and [complete manifest](verification/linux-2026-09-13/EVIDENCE-MANIFEST.json) bind 703 files plus the outer manifest, including all thirteen nested candidate manifests and all 524 committed project inputs. The original project ZIP has SHA256 `f4be34322f3b97935c20bcca0a9b3538ff010e69df0e822569716fb41df8135f`; the control ZIP has SHA256 `b948e6a6a81e9b138965f4bf1e98a9fe382d56bb51e889c4c50e9b9c541740da`. Both agree with GitHub metadata and actual upload logs. The complete 217-file run-log ZIP is retained with locally computed SHA256 `b204c7a65910570275a9354aa45db865219113b64e7701fa35e0a0b7b1fc99b3`; no GitHub-published digest for that log ZIP is claimed. All permanent-ID checks and 17 tests passed.

Operational reviewer /root/mf16_final_referee previously served as independent final mathematical referee 2 and candidate-document preparer. /root/formal_review_standards independently reviewed the concrete candidate packaging. Root, a disclosed proof coauthor, accepted the operational evidence and prepared these publication wrappers. These subsequent roles do not increase the two independent final mathematical referee approvals. The [root acceptance](verification/root-operational-2026-09-13/ROOT-CHECKS.json) and its complete manifest bind six files plus the outer manifest.

The actual Linux run verified the immutable candidate. Publication changes only README.md and formalization.yaml among its 524 inputs, archiving both exact originals under [publication evidence](verification/publication-2026-09-13/archive/). All 522 other candidate inputs, 704 Linux evidence files and seven root operational files remain unchanged. All 361 proof inputs, 31 statement inputs and 17 original source/policy inputs remain preserved through exact historical wrapper archives. The original mathematical suffix, source manuscripts and all nested manifests remain intact. Earlier pending notices are historical records.

Independent publication review precedes the publication commit, normal fork push and new upstream main PR. No new proof execution, external human review, official Tau Ceti endorsement or new mathematical priority is claimed by this documentation update.
