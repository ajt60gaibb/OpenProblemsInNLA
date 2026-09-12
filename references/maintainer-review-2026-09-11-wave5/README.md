# Independent maintainer review - follow-up submissions, 11 September 2026

These reviews check the actual submitted proofs and primary sources independently of the contributors' own AI reports. They are automated-agent reviews, not external human peer review or formal verification. Integration preserves all permanent IDs, canonical paths and original targets.

| PR | Original reviewed head | Result |
| --- | --- | --- |
| [93](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/93) | `387e68814c3f68ca0bfc09dabfc3fea5a97c64c2` | PASS: remaining integration provenance; the independently reviewed RA-12 proof is already published and unchanged. |
| [122](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/122) | `53dd2d078222d2346ffa20a05e602f9ae1766eef` | PASS: full complex Jordan-block GMRES equality and affine triangular-Toeplitz minimax theorem. |
| [125](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/125) | `96c83a5e5c4be73194f47d01e68a0a8f2a062e87` | PASS: Hall's essential Delta proof and both SP-11/SP-12 application notes. |
| [127](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/127) | `e5ad08c1a301d532ea200df8580224bb893b2240` | PASS: exact order-eight counterexample to the IE-05 extremizer equality. |
| [130](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/130) | `397c70a40e8ee785201800d20f798c7d9b73c22f`, integration delta `aa31885b42a212f14c5912a77d958c433605a2c3` | PASS: robust rare-event counterexample to the complete canonical IE-04 exponential tail. |

PR122: [complete mathematical review](pr122-review.md), [independent preservation checker](pr122-preservation-check.py), [176-case results](pr122-preservation-check.json), [seven-page PDF/source QA](pr122-pdf-qa.md), and [integration checks](pr122-integration-checks.json).

The primary Carathéodory–Fejér theorem was checked directly in Courtney–Sarason, Theorem CF, page 84. The new proof's singular-subspace description, scalar factorization, simultaneous complex moment preservation, finite-dimensional optimality argument and all target quantifiers were independently reconstructed. Numerical diagnostics supplement that analytic argument. Shared indexes were regenerated against published main; the 17 ID-safeguard tests passed.

PR125: [complete mathematical/source review](PR125-review.md), [source hashes](PR125-review-evidence.json), [independent leading-term checker](PR125-leading-monomial-check.py), [198-term results](PR125-leading-monomial-check.json), [ten-page PDF/source QA](pr125-pdf-qa.md), and [integration checks](pr125-integration-checks.json).

The review reconstructs the shared-variable leading-monomial argument, faithful PSD Gram construction and SAP implication in Hall's pinned preprint. Both applications preserve the exact real-symmetric graph patterns and all-graph quantifiers. The submersion argument includes rank-zero and disconnected cases. Hall retains theorem credit; Stepaniants receives application-note credit. The primary source remains a preprint, and its nonessential wording issues are documented in the review. Finite symbolic diagnostics supplement the analytic audit.

[PR122's completed merge record](pr122-merge-result.json) identifies the exact integrated head and successful required CI run.

PR127: [complete mathematical review](pr127-review.md), [independent exact checker](pr127-exact-check.py), [exact results](pr127-exact-check.json), [six-page PDF/source QA](pr127-pdf-qa.md), [recovered-variant review](PR127-recovery-review.md), and [integration checks](pr127-integration-checks.json).

The independently transcribed matrices establish both positive-diagonal QR conventions, all first-available-row pivot decisions and every active entry. The exact positive squared growth gap refutes the complete original extremizer equality; no true supremum or asymptotic leading constant is claimed. A mislabeled supporting JSON field was renamed to identify diag(T), the integer upper factor, correctly. Its numerical values and all proof/publication files are unchanged; the relation checker was rerun and the two current manifest hashes refreshed. Historical snapshots and raw recovered sources are preserved.

[PR125's completed merge record](pr125-merge-result.json) records its exact head and successful required CI. PR127's integration preserves the separately published IE-01 Lean verified status and the associated catalog support.

PR93: [final provenance-delta review](PR93-final-delta-review.md), [dated verification evidence](PR93-final-delta-evidence.json), and [current integration checks](pr93-integration-checks.json). The replacement workflow ran and rejected the outdated branch because it lacked later published IDs. Integrating current main restores all 217 mappings and passes all 20 repository tests without weakening the safeguards. All 761 published canonical artifacts remain byte-identical; only the ten dated RA-12 provenance files and these maintainer audit records are added. The earlier mathematical and PDF reviews continue to apply.

PR130: [complete mathematical and primary-source review](pr130-review.md), [independent exact checker](pr130-independent-check.py), [exact results](pr130-independent-check.json), [six-page PDF/source QA](pr130-pdf-qa.md), and [final integration checks](pr130-integration-checks.json). The analytic argument defeats every proposed positive constant pair using a full-dimensional Gaussian event with strict pivots. Finite exact checks supplement the universal argument. Both subsequent dated integration records were independently compared with their exact parent commits; every reviewed proof artifact and all 758 unrelated canonical artifacts remain unchanged. All 217 mappings and all 20 repository tests pass.

[PR93 completed merge record](pr93-merge-result.json) and [PR127 completed merge record](pr127-merge-result.json) identify their exact merged heads and successful required checks.
