# Independent maintainer review — third batch, 11 September 2026

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

PRs #93 and #103 remain outside integration while their required fork workflow executions await explicit approval. The same execution-approval condition applies to #68, #83, #85 and #91 from the [preceding batch](../maintainer-review-2026-09-11-wave2/README.md). Their mathematical reviews do not substitute for required checks. See the [latest pending-revision audit](../maintainer-review-2026-09-11-wave2/audit-root/current-pending-revisions.md) for corrected #85 fingerprints and the one stale #83 reference-summary sentence.

The newly arrived PR #111 is being reviewed separately and is not included in the decisions or counts above. The user's working checkout and uncommitted research changes were preserved throughout; all integration took place in an isolated clone.
