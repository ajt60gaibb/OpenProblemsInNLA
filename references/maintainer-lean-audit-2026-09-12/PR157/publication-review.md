# PR #157 / RA-03 publication review

**PASS — no publication, metadata, scope, dependency-pin, or PDF blocker found.**

- Exact reviewed head: `a49725405f153f8756610f52ce6cbc6463c51616`.
- Date: 12 September 2026.
- Reviewer: independent OpenAI Codex agent `/root/audit_tensors_complexity`; this is an AI-agent review, not external human peer review.
- Scope: publication claims, original-target preservation, export/manifest agreement, credits, pinned configuration, shared-file preservation, and visual inspection of the final canonical PDF. Separate agents audit the complete probability and spectral proofs; the coordinating reviewer checks current live CI and integration. This report does not claim a local Lean or Linux harness rerun.

## Original target and promotion scope

The canonical README from `## Problem statement` through its references and historical audits is **byte-for-byte unchanged** from published main `587bd896f0e1006f4a4b7f38555e3a523ef85176`. Difficulty, importance, rating rationale and topic are unchanged. RA-03 retains its ID, canonical path, arbitrary complex rectangular inputs, joint conditional entry probabilities, exact cross update, zero absorption, mean squared Frobenius error, all positive dimensions and admissible ranks, and decreasing singular-value tail.

The new status and evidence section describe a complete negative answer through the order-two, one-pivot witness. They do not claim to prove the proposed bound or merely a conditional reduction. Definitions, Challenge and Solution retain the universal conjecture, and the final export explicitly negates it. The description identifies expected squared residual `18/5`, actual rank-one tail `1`, and failure of the factor `2` at `k=1`.

The README, project guide, formalization manifest and resolution archive explicitly exclude the manuscript's stronger sharp all-rank `4^r` theorem and Cholesky results from the four formal exports. The older informal resolution is retained and its earlier verification disclaimer is dated, so it does not contradict the subsequent Lean verification.

## Four exports and metadata

The same four names occur, in the same order, in `Solution.lean`, `comparator.json`, `formalization.yaml` main results, and the canonical evidence list:

| Export | Advertised and declared scope |
| --- | --- |
| `NLA.RA03.frobeniusSq_eq_norm_sq` | Equality of the explicit complex-entry sum with the actual squared Frobenius norm. |
| `NLA.RA03.process_isProbability` | Nonnegative normalized conditional masses and complete-history masses for every input and history length. |
| `NLA.RA03.counterexample` | Witness nonzero entries, Gram matrix, actual ordered singular values, all four pivot masses/errors, expectation, tail and strict violation. |
| `NLA.RA03.not_squaredErrorConjecture` | Negation of the complete universal target. |

Challenge and Solution type texts match after whitespace normalization. Each public export aliases the corresponding `_proved` declaration. All four have individual main-result records, axiom lists and Comparator links in `formalization.yaml`; none is omitted or represented only by an informal claim. Comparator selects all four, permits no definition holes and allows only `propext`, `Classical.choice`, and `Quot.sound`.

Mathematical credit remains with Matthew J. Colbrook and the original conjecture with Gilles and Wilber. George Stepaniants is credited specifically for the Lean formalization. The canonical page and manifest give affiliations and disclose AI assistance, independent agent review, lack of external human peer review, and the distinction between remote Linux execution and local inspection of downloaded evidence. The source links and proof links use immutable revisions.

## Configuration and evidence consistency

The Lakefile is declarative TOML with default target `Solution`. The toolchain, README and manifest consistently identify Lean 4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. All ten manifest dependencies use HTTPS GitHub URLs and exact 40-character revisions. The four intentional Challenge placeholders are in the separate target module; Solution imports Proof, not Challenge.

The archived Linux receipt for proof revision `973f95969701601dcae7b30683b175843baa9c22` records `comparator-accepted` with the same four-export configuration. I independently compared its hashes for Definitions, Proof, Challenge, Solution, Comparator configuration, toolchain, Lakefile and dependency manifest against the reviewed head: **all eight core inputs match**. The linked axiom log lists only the three allowed axioms for all four public exports and eight audited internal declarations. Current live-run identity and complete operational verification remain the coordinating reviewer's separate check.

The PR changes no shared tool, test, workflow, numbering registry, AGENTS instruction, or contribution policy relative to current main. The apparent unrelated differences in a direct old-head/current-main comparison are prior promotions absent from the PR's older base, not part of its three-dot patch.

The PR's generated totals (`86 Solved`, `3 Lean verified`) correctly reflect its branch base `02b8077`. At finalization I independently checked the integration checkout: all **124 RA-03 directory files remain byte-identical** to the reviewed head, and canonical statuses, root summary and catalog summary agree on **83 Solved, 6 Lean verified, 57 Open and 71 Partially resolved**. All 128 open/partially resolved targets and the prior three Lean promotions are retained.

## Final PDF

Rendered and visually inspected **both pages** of the actual committed `randomized-and-low-rank-approximation/RA-03/problem.pdf` with Poppler. It is a two-page A4 PDF. The mathematical title, small matrices, exponents, norm expressions, four declaration names, credits, long reproduction commands and original target are legible. No clipping, overlap, missing glyph, broken equation, or orphaned heading was found. The evidence section ends cleanly on page one; the historical resolution and preserved original problem begin on page two. Status, content and scope agree with the canonical README.

No repository file or Git state was changed. Only temporary page images and this review were written outside the checkout.
