# Independent maintainer review - follow-up submissions, 11 September 2026

These reviews check the actual submitted proofs and primary sources independently of the contributors' own AI reports. They are automated-agent reviews, not external human peer review or formal verification. Integration preserves all permanent IDs, canonical paths and original targets.

| PR | Original reviewed head | Result |
| --- | --- | --- |
| [122](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/122) | `53dd2d078222d2346ffa20a05e602f9ae1766eef` | PASS: full complex Jordan-block GMRES equality and affine triangular-Toeplitz minimax theorem. |
| [125](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/125) | `96c83a5e5c4be73194f47d01e68a0a8f2a062e87` | PASS: Hall's essential Delta proof and both SP-11/SP-12 application notes. |

PR122: [complete mathematical review](pr122-review.md), [independent preservation checker](pr122-preservation-check.py), [176-case results](pr122-preservation-check.json), [seven-page PDF/source QA](pr122-pdf-qa.md), and [integration checks](pr122-integration-checks.json).

The primary Carathéodory–Fejér theorem was checked directly in Courtney–Sarason, Theorem CF, page 84. The new proof's singular-subspace description, scalar factorization, simultaneous complex moment preservation, finite-dimensional optimality argument and all target quantifiers were independently reconstructed. Numerical diagnostics supplement that analytic argument. Shared indexes were regenerated against published main; the 17 ID-safeguard tests passed.

PR125: [complete mathematical/source review](PR125-review.md), [source hashes](PR125-review-evidence.json), [independent leading-term checker](PR125-leading-monomial-check.py), [198-term results](PR125-leading-monomial-check.json), [ten-page PDF/source QA](pr125-pdf-qa.md), and [integration checks](pr125-integration-checks.json).

The review reconstructs the shared-variable leading-monomial argument, faithful PSD Gram construction and SAP implication in Hall's pinned preprint. Both applications preserve the exact real-symmetric graph patterns and all-graph quantifiers. The submersion argument includes rank-zero and disconnected cases. Hall retains theorem credit; Stepaniants receives application-note credit. The primary source remains a preprint, and its nonessential wording issues are documented in the review. Finite symbolic diagnostics supplement the analytic audit.

[PR122's completed merge record](pr122-merge-result.json) identifies the exact integrated head and successful required CI run.
