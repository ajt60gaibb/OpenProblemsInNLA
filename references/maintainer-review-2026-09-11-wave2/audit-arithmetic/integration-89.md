# Independent structural audit of staged PR 89 integration

Date: 2026-09-11. Main HEAD: `16369809e6e600144bd350ab70b7473b652f46f1`. Staged MERGE_HEAD: `3443179cb62b410678f3c67f26cd8df56ba6133a`. Their merge base is `ab754fabe3d48dc8d6eab6bcffce583e46d2b88f`.

**Verdict: structural PASS.** This review checks preservation and catalog integration only; it does not replace the separate proof review or full permanent-certificate reruns.

I read the staged index directly, using Git blob IDs and modes rather than the mutable working-tree files. All 227 nonshared contributed paths exactly match PR 89's source blobs and modes. The staged diff has precisely the same 231 path set as the PR contribution against its actual merge base. The four shared paths are CATALOG.md, README.md, RESOLVED.md and the arithmetic category README. There are no unexpected changes, deleted main files, unresolved index stages, or changes to any previous file outside the PR's contribution. In particular, all previously merged manuscripts, proof files, verification records and review records remain intact.

All 203 original problem IDs retain their exact category paths and first-line headings. The permanent-ID registry is unchanged. Comparing all original canonical problem READMEs with their staged versions finds no removed/replaced nonblank original text apart from the intended Status and Last checked fields. The original mathematical targets, ratings, rationales and source-reference text remain intact.

Every one of the 203 staged catalog rows and corresponding category rows agrees with the canonical title, ID/path, status and ratings, and occurs exactly once. Independent status counts are 75 Open, 78 Partially resolved, 49 Solved and one Solution claimed. Both top-level overview summaries correctly report 153 open targets and 50 other retained entries. AA-01 is Solved; AC-11 and AC-12 remain Partially resolved. These are structural checks of the intended classifications, not independent certification of the permanent computations still being rerun elsewhere.

The complete new AA-01 RESOLVED section from PR 89 occurs exactly once, and no nonblank line from main's RESOLVED content is removed. The references index is unchanged and retains the prior review-batch link. PR 89 adds no change to either shared rendering tool, and both staged renderers exactly match current main. PF-05, SF-01, RE-05 and IE-20 special page-break rules each remain present once.

The index inventory was unchanged from the beginning to the end of this audit. SHA-256 of the raw `git ls-files --stage -z` inventory: `0d5f26b65d31c03b0811befffa79c218aa68b6f0dc7053334ee027ae7335a8a5`. Detailed machine-readable evidence is in `integration-89.json` beside this report. This fingerprint binds the check to the observed staged source/index state; later maintainer audit-document additions are outside it.

No shared working-tree/index file was modified, no commit was created, and no external action was taken by this reviewer.
