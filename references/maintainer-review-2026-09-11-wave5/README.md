# Independent maintainer review - follow-up submissions, 11 September 2026

These reviews check the actual submitted proofs and primary sources independently of the contributors' own AI reports. They are automated-agent reviews, not external human peer review or formal verification. Integration preserves all permanent IDs, canonical paths and original targets.

| PR | Original reviewed head | Result |
| --- | --- | --- |
| [122](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/122) | `53dd2d078222d2346ffa20a05e602f9ae1766eef` | PASS: full complex Jordan-block GMRES equality and affine triangular-Toeplitz minimax theorem. |

PR122: [complete mathematical review](pr122-review.md), [independent preservation checker](pr122-preservation-check.py), [176-case results](pr122-preservation-check.json), [seven-page PDF/source QA](pr122-pdf-qa.md), and [integration checks](pr122-integration-checks.json).

The primary Carathéodory–Fejér theorem was checked directly in Courtney–Sarason, Theorem CF, page 84. The new proof's singular-subspace description, scalar factorization, simultaneous complex moment preservation, finite-dimensional optimality argument and all target quantifiers were independently reconstructed. Numerical diagnostics supplement that analytic argument. Shared indexes were regenerated against published main; the 17 ID-safeguard tests passed.
