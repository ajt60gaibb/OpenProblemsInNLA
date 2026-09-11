# Repository exclusion audit

**Result: INCOMPLETE. RA-02 and RA-03 are not cleared for submission.**

This record concerns the repository `ajt60gaibb/OpenProblemsInNLA` and the randomized-and-low-rank-approximation category. Observations were made during the 11 September 2026 research session. A current main-branch commit could not be pinned. The record is not a certification of the repository's current unresolved-problem status.

## Exclusions applied

The retrieved RA issue-search listing showed the following solution-related submissions. Titles/descriptions below are paraphrases of the listing, not assertions that the underlying mathematical work has been independently validated. The user requested exclusion whenever a solution is listed; partial-solution entries were also excluded conservatively.

| Problem | Listed record | Observed listing description | Treatment |
|---|---|---|---|
| RA-07 | [Issue #26](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/26) | Reviewed resolution of the volume-sampling convexity question; closed | Excluded |
| RA-08 | [Issue #27](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/27) | Reviewed spectral-transfer resolution; closed | Excluded |
| RA-09 | [Issue #28](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/28) | Reviewed Frobenius-transfer resolution; closed | Excluded |
| RA-10 | [Issue #30](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/30) | Reviewed partial nuclear-transfer bound; open | Excluded, including the unresolved remainder |
| RA-12 | [Issues #31](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/31) and [#92](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/92) | Gamma auxiliary counterexamples and a complete Gaussian trace-tail comparison submission; open | Excluded |
| RA-13 | [Issue #31](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/31) | Shared RA-12/RA-13 auxiliary counterexample submission; open | Excluded conservatively |

The source listing was the [RA issue query](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues?q=is%3Aissue+RA). The raw initial browser response is not archived here. Later reads of this listing and related pages failed. The exclusions remain applied even though the underlying issue bodies were not all obtained.

## Targets and unresolved gaps

The retrieved category listing describes RA-02 as a polynomial-factor same-rank RPCholesky question and RA-03 as an improvement of the RPLU squared-error factor to `2^r`. The retrieved RA issue listing did not display a matching RA-02 or RA-03 solution. **That observation is not an exhaustive absence check.** A title-only or identifier-only query can miss comments, attachments, and omnibus submissions.

The exact files below could not be obtained:

- `randomized-and-low-rank-approximation/RA-02/problem.tex`
- `randomized-and-low-rank-approximation/RA-03/problem.tex`

Consequently their exact current hypotheses and editorial status must still be compared with the theorem. The RPLU paper's entry-squared algorithm, Theorem 3, and explicit `2^r` conjecture were obtained separately, so the stand-alone mathematical counterexample does not depend on an assumed repository wording.

The closed-PR listing identified two important broad submissions whose full contents/files could not be inspected:

| PR | Retrieved listing description | Why it blocks clearance |
|---|---|---|
| [#6](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/6) | Records 18 reviewed resolutions and four partial results; merged | The title does not identify all covered problems |
| [#32](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/32) | Records four reviewed resolutions and scoped transfer results; merged | The complete set of covered problems and attachments was not read |

It would be unsafe to infer that neither PR covers RA-02 or RA-03. The initial category listing and issue/PR counts appeared to reflect different update states, so the category page was not used as proof of eligibility. A partial view of `RESOLVED.md` was insufficient to close the gap.

## Other category entries

No solution is claimed for RA-01. Its oversampling formulation was obtained, but the same-rank results in this package do not settle it. Other entries visible in the initial category inventory—KE-05; RA-04, RA-05, RA-06, RA-11, RA-14, RA-15, RA-16, RA-17; RE-01, RE-02, RE-03, RE-05, RE-06; and TR-01, TR-03, TR-07, TR-08—are not addressed in this submission package and are not certified eligible. A later PR listing also referred to an RA-18 addition, not present in that initial inventory.

## Fetch evidence

Later browser requests to the repository, problem sources, issues, PR files, and patch views returned fetch failures, commonly `Cache miss`. Such failures were not interpreted as zero results. A direct read-only API attempt also failed before receiving any issue records; see `session_fetch_attempt/report.json`. No current GitHub content is fabricated or reconstructed from that failure.

## Complete the audit before posting

Run the read-only collector in a fresh directory:

```sh
python recheck_github.py --out fresh_audit
```

For repositories with many PRs, unauthenticated rate limits may interrupt collection. An optional `GITHUB_TOKEN` can be supplied through the environment; use only read access. The utility does not print the token and restricts requests to HTTPS GETs for this fixed repository on `api.github.com`. It refuses redirects and saves response hashes. No remote write method is implemented.

A successful collection ends with `FETCHED_REQUIRES_HUMAN_REVIEW`, never `ELIGIBLE`. Read all saved issue/PR bodies and comments, review the changed files, inspect linked solution attachments, and check omnibus PRs even when they do not mention the problem identifiers in their titles. Compare the pinned source statements with the manuscript, check repository contribution rules, and recheck for intervening submissions immediately before posting.

If a prior solution is listed for either target, withdraw that draft from the proposed unresolved-problem submissions. Preserve the mathematical note only as separately attributed research, without claiming that the repository problem was newly resolved here.
