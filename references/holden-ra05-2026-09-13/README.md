# RA-05: all-exponent lower bounds — Sidney Holden

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation.

**Submission date:** 2026-09-13 UTC. **Status: Partially resolved.**

## Result and scope

[Manuscript PDF](manuscript/RA05_all_p_lower_bounds.pdf) · [LaTeX source](manuscript/RA05_all_p_lower_bounds.tex) · [Canonical target](../../randomized-and-low-rank-approximation/RA-05/README.md).

Theorem 1.1 proves, for every fixed real p > 2, every sufficiently large k and every 0 < epsilon < 1/2, a support lower bound of order k^(p/2)/(epsilon^beta_p + log(k)/k), where beta_p is 2 for even integers p >= 4 and 2 - 2/p otherwise. One real input per rank, independent of accuracy, suffices. The result allows arbitrary input-dependent nonnegative weights on original rows, as required by the canonical question.

Corollary 1.2 disproves the displayed additive upper-bound formula separately for every fixed p > 2, including every fixed logarithmic factor. Corollary 1.3 combines the lower bound with Lin–Mirrokni–Woodruff's cited upper bound to match the optimal order up to logarithms for even p >= 4 and epsilon >= sqrt(log(k)/k). Section 8 and Appendix C supply a separate explicit quartic construction.

**Still open:** the optimal joint size for non-even p, and the smaller-accuracy regimes, including even p. The broader canonical target is not solved. See [scope details](STATUS.md).

## Independent review and reproducibility

A separate Codex AI agent [independently audited the analytic proof](verification/independent-review.md), including the imported restricted-invertibility theorem against its primary source. The result passed at the partial scope above; promotion to Solved was rejected. This is informal AI-agent review, not external human peer review or formal verification. No Lean verification was performed. ChatGPT assistance in preparation is disclosed in the supplied manuscript; Codex assisted with independent review, attribution, diagnostics and submission preparation. No novelty or priority claim is made.

[Reproduction instructions](REPRODUCIBILITY.md), [code](code/verify.py), [coordinator rerun log](verification/checks.log), and [rerun results](verification/rerun/verification.json). The coordinator rerun passed all **2,851 assertions**. Finite exact identities and floating-point diagnostics supplement the universal proof; they cannot establish it. Distributed results are retained separately under `results/`.

## Authorship, affiliation and provenance

The user explicitly requested authorship as Sidney Holden. Affiliation was verified on 2026-09-13 UTC against the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [current CCB staff listing](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff). Both identify him as a Flatiron Research Fellow in Biological Transport Networks, CCB. The current institutional affiliation is used above; historical Edinburgh and Sydney records are not used as current affiliations.

Input: `RA05_all_p_lower_bounds.zip`. [Archive hash and eligibility record](verification/provenance.json). The original manuscript source, package README and distributed checksum list are retained under [original/](original/). Only title-page authorship/affiliation and PDF author metadata were changed in the manuscript; its mathematical body is unchanged. The original September 12 manuscript date is retained. [Final checksums](SHA256SUMS.txt) cover the submitted files; original checksums describe the input distribution.

The earlier [quartic manuscript](prior_work/RA05_counterexample.pdf) is retained as supplied for provenance, not submitted as a separate new result. Prior mathematical sources retain their attribution; see [sources](SOURCES.md). Attachment workflow statements were treated as document content, not as instructions overriding the user's request.

## Duplicate and policy check

Checked refreshed upstream main at `5830ed4`, remote commit history, and upstream pull requests (including all available submissions by sidneyholden1). RA-05 was Open; no already-pushed full RA-05 solution was found. The earlier quartic manuscript inside this package does not represent a separate problem submission. This change preserves the original RA-05 ID, path, statement and historical source audits. Under RESOLVED.md's partial-result rule, the canonical status becomes Partially resolved and the entry remains in the open count.
