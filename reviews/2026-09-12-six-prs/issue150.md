# Issue #150 assessment: TR-08 precision of the target

Date: 12 September 2026. Reviewer: independent Codex agent `audit_tr03`. Read-only assessment of current issue #150, merged PR #151, published TR-08, and the primary source.

**Verdict: the issue is fully addressed and can be closed as completed. The mathematical problem remains Open.** There is no outstanding requested edit in the current issue body or comments.

Issue: [#150](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/150). It asks whether a full resolution must match necessary and sufficient sparsity conditions, and whether constants or logarithmic gaps can be ignored. This is a request for precision in the completion criterion, not a request for a proof of the threshold.

Merged fix: [PR #151](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/151), merge commit `e7252e5307781a7c897bca6cb124f6ab838f6809`, merged 12 September 2026 at 15:10:05 UTC. It changes TR-08's Markdown, TeX, PDF, and adds TR-08 to the renderer's existing reference-section page-break list. The published base reviewed was `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.

Evidence in the current [canonical entry](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/randomized-and-low-rank-approximation/TR-08/README.md#precision-of-the-target):

- Lines 25-29 define complete resolution as an explicit asymptotic criterion equivalent to the displayed probability property for some fixed positive lower-singular-value constant.
- They state that separate bounds with an undecided gap are partial progress, and that constants or logarithmic factors must be resolved when they affect whether that property holds. Optimizing the value of the positive singular-value constant is unnecessary.
- They explain that identifying a critical logarithmic exponent is an intermediate objective and can leave the critical scale, constants, or log-log corrections unanswered. The existence of such an exponent is not assumed.
- The unchanged original statement at lines 13-23 still uses independent fixed-size column supports, independent signs, normalized columns, an independently sampled `k/100`-column submatrix, and the original probability bound. The ID/path and Open status are retained.
- Lines 43-45 explicitly record the issue response as a clarification and distinguish it from a solution or a new literature-wide status audit.

I independently retrieved [Huang, Rudelson, and Tikhomirov, §7, Problem 7.2 and its following paragraph](https://arxiv.org/html/2607.05384v2). The source asks for optimal necessary and sufficient growth conditions in the same fixed-sparsity random-column model; its following paragraph proposes a critical logarithmic power. The clarification accurately distinguishes the exact asymptotic characterization from this intermediate exponent objective. It does not replace the published mathematical target.

The [owner's reply](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/150#issuecomment-5646728025), posted at 15:10:29 UTC, already answers the reporter's question, links the merged clarification, and explains both levels of precision. No later objection or follow-up appears in the current issue comments. Thus an additional mathematical edit or a duplicate explanatory comment is unnecessary; administrative closure is the remaining action.

Following the PDF skill, rendered both pages of the current published TR-08 PDF and inspected them completely. The completion criterion and logarithmic-exponent discussion appear legibly on page 1; source, historical audit, and dated clarification appear on page 2. No clipping, overlap, or missing formulas/glyphs were found. QA images are under `/private/tmp/nla-sept12-audit.JfqvTr/reports/tr03-pdf/tr08-*.png`.

Recommended disposition: close issue #150 as completed with PR #151 as the resolution reference, while preserving `**Status:** Open` on TR-08. No issue mutation or public comment was made by this reviewer.
