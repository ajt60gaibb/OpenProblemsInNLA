# Independent maintainer review — third batch, 11 September 2026

**Latest disposition:** the [branch-update reconciliation](latest-head-reconciliation.md)
records five accepted replacement heads and the still-pending replacement workflow
for PR93. Its originally reviewed, approved proof is included, but the current PR
remains open until that replacement gate clears. Earlier six-PR and eighteen-PR
acceptance statements refer to the recorded original submission commits.

This batch reviews six further solution PRs against their unchanged canonical targets. Complete arguments and primary-source applicability were checked independently of the contributors' embedded PASS reports. The review combines analytic mathematics, independently written exact checks, inspected certificate reruns and final PDF inspection. It is **AI-agent mathematical review, not proof-assistant certification, external human peer review or a determination of priority**.

| PR and reviewed head | Detailed report | Supported result |
| --- | --- | --- |
| [#93](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/93), `c797aee814c8bebe4452329c93f5d84fd9c41f1f` | [RA-12](audit-root/PR-93.md) | Complete Gaussian trace-tail comparison at epsilon >= 2/(m mu), including equality. Threshold optimality is not claimed. |
| [#97](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/97), `04981f27fd4a1117705dd24139fd752fc2bc3459` | [TR-06, TR-15, TR-26](audit-tensors/PR97-audit.md) | Finite mean angular conditioning; an admissible negative Hankel counterexample; both reduced discriminant degrees. |
| [#101](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/101), `e62f9db721430d40c94e103249bc79586d1d97b3` | [TR-04, TR-13, TR-20](audit-tensors/PR101-audit.md) | Strict pointwise TT improvement, generic Hankel rank equalities and both reduced nonisotropic degrees. No uniform smaller TT factor or exceptional-tensor claim is made. |
| [#103](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/103), `6f5861fa392db467dc23abd096a02a08573146b8` | [RA-10](audit-root/PR-103.md) | Full unordered nuclear-error transfer with C=11, including selected zero eigenvalues and f(0)>0. Neither optimality nor other norms are claimed. |
| [#106](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/106), `cf3c599b785be5b92c22e24dfcecb9ebecb7eef0` | [RA-02, RA-03](audit-random-pivot/PR106-RA02-RA03.md) | Negative canonical resolutions and sharp same-rank 2^r/4^r suprema, including the correlation extension. No oversampling result is asserted. |
| [#110](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/110), `7d00fde9b72f55268dca3c61cd57e93085aeec87` | [MF-05, MF-07, MF-12](audit-functions/PR110-REVIEW.md) | Uniform JSR growth and Hölder bounds; every nonnegative real growth exponent with every-length bounds. MF-06 is separate. |

All six mathematical reviews pass. Each report explains the quantified scope, boundary cases and source dependencies. A separate maintainer task provided [additional adversarial reviews of #93 and #103](independent-sept11/ROOT-REVIEW.md), including independently written exact and high-precision compression diagnostics.

## Reproducible evidence

- The two tensor submissions pass 552 independent exact checks and 95 source/PDF checks; all 41 final PDF pages were rendered and visually inspected. The six proofs include full generic-multiplicity and boundary arguments where reduced discriminant degrees require them.
- Random pivoting passes the complete ten-test submitted suite, including the rank-eight certificate, plus independent all-pivot rational recursion, symbolic prefix-minor, history-count and replication checks. All 22 PDF pages were inspected.
- Matrix growth passes all submitted diagnostics, including all 33,554,430 nonempty binary words through length 24, plus independent exact block damping, gap-budget, Jordan and lower-word checks. All 18 PDF pages were inspected and their text reproduced from unchanged TeX.
- The two root-reviewed manuscripts pass 26 recomputed current document fingerprints in total; all 17 PDF pages were inspected. Their universal theorems rest on the analytic arguments, not finite diagnostic sampling.

Check sources, results, logs and PDF QA manifests are retained beside the reports. Transient snapshot paths, rendered page images and build directories identify the original local review environment; large scratch files are not republished here. No submitted program was executed before its source was inspected.

## Integration and permanent identities

PRs #97, #101, #106 and #110 have passed the existing required numbering checks and are integrated through ordinary merge commits. Their eleven solved entries retain their original IDs, paths, questions, historical ratings and earlier attributed results. Shared indexes are regenerated from canonical metadata, and additive resolution records are combined.

All **203 previously published IDs** are preserved. This solution integration yields **60 solved**, **68 open**, **74 partially resolved** and **one solution claimed** entry. The 142 open/partially resolved targets remain in the catalog. No gap is filled and no solved entry is renumbered or removed. The permanent-ID registry and required workflow are unchanged.

The six previously pending submissions #68, #83, #85, #91, #93 and #103
are now included after explicit workflow-execution approval and successful
required checks. See the [final six-PR integration record](final-six-integration.md)
for the exact heads, preserved source checks, corrected historical summaries
and AA-01's combined two-proof canonical page.

Across the second and third batches, 18 PRs are accepted. The final integration
retains **203 entries: 67 solved, 65 open, 70 partially resolved and one solution
claimed**, with all 203 original IDs and paths unchanged. All 17 numbering tests
pass. The earlier counts above describe the initial four-PR integration.

The newer continuing audit task owns #111, #114, #116 and #118, which are outside
this integration. Its #111 repair must account for our exact RA-20 counterexample:
the proposed n=s=3 count is three rather than four. All supporting findings were
passed to that task. The user's working checkout and uncommitted research changes
were preserved throughout; integration used an isolated clone.
