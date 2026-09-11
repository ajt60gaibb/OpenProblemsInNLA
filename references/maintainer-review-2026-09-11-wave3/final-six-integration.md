# Final integration of the six previously pending PRs

Integration commit before the final audit-record commit: `d65e757a425d0cf709ac4969399b37cbce7b684c`.
Published comparison base: `87366c62d3b5c47d170f747b1cb40ab38d501013`.

The six required GitHub Actions runs were explicitly authorized by the user in the audit task where that consent was given directly. That task performed the approvals. Independent API reads then confirmed all six runs completed successfully at the exact reviewed commits; see [run results](six-authorized-workflow-runs.json) and the [read-only workflow inspection](independent-sept11/WORKFLOW-CHECK.md). No protection was weakened and no required check was substituted or bypassed.

| PR | Reviewed head | Resolution |
| --- | --- | --- |
| #68 | `2a1a0b39992bbd5654e7bdf9f869e21a6cee0d71` | AA-01, MD-03 and MD-04; AA-01 keeps both separately attributed proofs under one ID. |
| #83 | `eadd702330dfdc56de30e429d4fb08340c66eafb` | IE-15 exact growth factors, retaining the earlier order-five evidence. |
| #85 | `58a65609730306db4004352ccbdb5d8273ca2ff4` | MI-28 full original determinant target; all prior fingerprint findings corrected. |
| #91 | `cc5ed78e4ca055f15717e5130f69bff6097d9406` | MI-24 full Schatten target. |
| #93 | `c797aee814c8bebe4452329c93f5d84fd9c41f1f` | RA-12 complete Gaussian relative-tail comparison. |
| #103 | `6f5861fa392db467dc23abd096a02a08573146b8` | RA-10 full unordered nuclear-error transfer with C=11. |

All six reviewed heads are preserved as ancestors by ordinary merge commits. The [structural check](integration-six.json) verifies that all 88 nonshared contributed files preserve their reviewed bytes and modes. Shared generated indexes, additive resolution records and rendering configuration were reconciled separately. The optional email template retains the existing multi-line conditional form; the RA-10 page-break adjustment from its submission is preserved.

AA-01's canonical README contains both complete attributed notices, including every manuscript/review/provenance link and the limitation about missing historical experimental programs. Its full original target is unchanged. The only change in its earlier literature section is the historical heading's addition of “Earlier.” The entire previously published Colbrook arithmetic source tree and every incoming Stepaniants proof file remain unchanged. The canonical TeX/PDF was rebuilt from the combined README, with a page break before the unchanged target. Both final pages were rendered and visually inspected: no clipping, overlap, missing formulas or conflict markers. See [PDF QA](aa01-final-pdf-qa.json) and the [additional preservation review](independent-sept11/AA01-INTEGRATION.md).

For IE-15, the older Colbrook reference summary now says its order-five witness alone left the target open and links the subsequent exact solution. The canonical page and RESOLVED.md already make that historical distinction and were rechecked. The order-five witness, source files and author attribution are retained. No mathematical proof was rewritten.

The original **203 permanent ID/path pairs**, registry, validator, required workflow and 17-test safeguard suite remain unchanged. The final local validator and all 17 tests pass against published main. The eight affected original mathematical targets were also independently compared with the published base and retained verbatim. AA-01 is counted only once.

Across the second and third review batches, **18 PRs** are accepted: #40, #47, #54, #62, #64, #68, #78, #81, #83, #85, #89, #91, #93, #97, #101, #103, #106 and #110. At this integration point the catalog has **203 entries: 67 solved, 65 open, 70 partially resolved and one solution claimed**. The earlier pending-workflow notes are historical; all six of these holds are resolved.

New submissions #111, #114, #116 and #118 belong to the newer continuing audit task and are outside this integration. The independent #111 audit found a concrete error in proposed RA-20: its n=s=3 full-Frobenius smooth-locus count is three rather than four, despite the cited source claiming four. The complete counterexample and all review evidence were passed to that task for correction; it must not be treated as an unchanged verified open question. Additional independent #114/#116 reviews were also delivered to the continuing task. No claim about those PRs' eventual integration is made here.
