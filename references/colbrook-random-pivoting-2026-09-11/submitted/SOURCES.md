# Sources

## Primary mathematical sources

1. Yifan Chen, Ethan N. Epperly, Joel A. Tropp, and Robert J. Webber. **Randomly pivoted Cholesky: Practical approximation of a kernel matrix with few entry evaluations.** *Communications on Pure and Applied Mathematics* 78(5), 995–1041, 2025. DOI: [10.1002/cpa.22234](https://doi.org/10.1002/cpa.22234). Author preprint: [arXiv:2207.06503](https://arxiv.org/abs/2207.06503). The retrieved arXiv PDF is version 6, dated 22 October 2024. Lemma 5.5 is the `2^r` same-rank trace-error upper bound; the lemma and its proof were checked in the PDF.

2. Marc Aurèle Gilles and Heather Wilber. **Low-Rank Approximation by Randomly Pivoted LU.** [arXiv:2601.22344](https://arxiv.org/abs/2601.22344), 2026. The abstract record and an [author-posted full-text copy](https://www.researchgate.net/publication/400339985_Low-Rank_Approximation_by_Randomly_Pivoted_LU), typeset with date 2 February 2026, were retrieved. Equation (3) and Algorithm 1 define the entry-squared sampling and rank-one update. Theorem 3 bounds the expected **squared** Frobenius error by `4^r` times the optimal squared error. The discussion immediately after that theorem conjectures replacement by `2^r`. The numerical calculations and sharp lower-bound constructions in this archive are derived here, not quoted from that paper.

3. **Open Problems in Numerical Linear Algebra**, [randomized and low-rank approximation category](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/randomized-and-low-rank-approximation), entries RA-02 and RA-03. A category-level listing was retrieved during the 11 September 2026 session. The exact current per-problem source files were not retrieved, and issue/PR coverage was incomplete. The archive's theorem statements are self-contained; the proposed mapping to repository resolutions remains subject to preflight.

## Repository-audit sources and gaps

The retrieved [RA issue search](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues?q=is%3Aissue+RA) listed existing solution or partial-solution submissions for RA-07, RA-08, RA-09, RA-10, RA-12, and RA-13. Those entries were excluded. The [closed-PR listing](https://github.com/ajt60gaibb/OpenProblemsInNLA/pulls?q=is%3Apr+is%3Aclosed) identified omnibus merged PRs [#6](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/6) and [#32](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/32), whose complete contents/files could not be read. The detailed audit record is in `audit/eligibility.md`.

The listing observations are not an immutable commit-pinned snapshot. Raw browser responses from the initial successful listings are not reproduced in this archive. Later requests returned fetch errors; a separate failed direct API attempt is preserved in `audit/session_fetch_attempt/report.json`. A failed request is not treated as an empty search result.

## Official documentation for the read-only audit utility

The API behavior was checked against GitHub's official documentation on 11 September 2026:

- [Issues](https://docs.github.com/en/rest/issues/issues): repository issue listings also contain pull requests, distinguishable by the `pull_request` key; use `state=all` and pagination.
- [Issue comments](https://docs.github.com/en/rest/issues/comments): repository-wide conversation comments include issue and PR conversations.
- [Pull-request review comments](https://docs.github.com/en/rest/pulls/comments) and [review bodies](https://docs.github.com/en/rest/pulls/reviews): these are collected separately.
- [Pull requests](https://docs.github.com/en/rest/pulls/pulls): changed-file listings are paginated and have a maximum of 3,000 files.
- [Repository contents](https://docs.github.com/en/rest/repos/contents): source files can be read at a pinned commit. The documented API-version header used in the utility is `2026-03-10`.

The utility is a collection aid only. Keyword matches do not establish the absence of a solution, and external attachments still need human inspection.
