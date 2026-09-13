# RA-09 — Lean formalization of concave Frobenius error transfer

**Complete proof, with two sealed independent AI-agent mathematical approvals. The coordinator has accepted both reports; authoritative Linux verification is pending.** The canonical problem remains **Solved**. This candidate adds a formalization of its full original target.

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

Implementation/route contributors /root/leancert_examples, /root, /root/formal_review_standards and /root/solved_statement_inventory are ineligible as independent final referees. The final referees are /root/ra09_final_referee1 and /root/mf16_final_referee. The latter now prepares these candidate documents; that role adds no mathematical approval. [Coordinator acceptance](verification/final-review-acceptance.json) binds both reports and their complete evidence. Actual non-root Ubuntu Comparator/default-kernel replay and rejection controls, operational review and publication remain pending.

The frozen OrderedExistence.lean header calls Colbrook's result a “counterexample”; this is a disclosed, nonblocking copied comment typo for the affirmative theorem. Frozen Lean bytes remain intact. The exact old README is [archived](verification/pre-candidate-README.md). NUMERICAL_TARGETS.md, SourceCorrespondence.md, PROOF_MAP.md and older handoffs retain their dated phase descriptions; the current status is stated here and in [formalization.yaml](formalization.yaml).

## Reproduction and pins

Lean is 4.33.1; Mathlib is 0df444a360eaa60ab8c11dca51a86af692955474 and LeanCert is 621a43d7cf21f87872392a01e874f2f1dbddc926. [lake-manifest.json](lake-manifest.json) pins all ten dependencies. With those dependencies installed, explicitly build the proof:

```sh
lake build Solution
```

The unchanged default target is Challenge. The authoritative check must run on the immutable candidate using the repository's [Linux workflow](../../../.github/workflows/lean-verification.yml) and [pinned verification instructions](../../../docs/lean/README.md). Local builds and these reviews do not stand in for that check.

The [source correspondence](SourceCorrespondence.md) credits the original manuscript, Mathlib construction and locally adapted RA-08 spectral design. Pinned examples are [Schiffer](https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1) and [Forsythe](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof). Review follows the repository's adaptation of [Tau Ceti](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics); metadata uses the pinned [v0.4 standard](https://github.com/mathlib-initiative/formalization.yaml/tree/99c678e569c7c4c0772db297c5ddd5e4c9b6322e). No external human review, official endorsement, current public-fork search or new mathematical priority is claimed.
