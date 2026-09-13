# RA-05: unrestricted quartic coresets — Sidney Holden

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation.

**Submission date:** 2026-09-13. **Whole-entry status: Partially resolved.**

[Manuscript PDF](manuscript/RA05_unrestricted_quartic.pdf) · [Proof source](manuscript/RA05_unrestricted_quartic.tex) · [Canonical target](../../randomized-and-low-rank-approximation/RA-05/README.md) · [Independent review](verification/independent-review.md).

## Exact scope

Theorem 1.1 and Sections 2–8 establish, for p = 4, arbitrary input rank, every integer k >= 1 and every 0 < epsilon < 1/2, the optimal worst-case strong original-row coreset size

    min(k^2 / epsilon^2, k^(5/2) / epsilon + k / epsilon^2)

up to logarithmic factors. All weights are nonnegative; the guarantee holds simultaneously for every subspace of dimension at most k, with no dependence on input row count or ambient dimension. The second upper branch has at most a fifth logarithmic power; combining it with the imported first branch gives a ninth power overall. Both lower constructions are proved in Section 8. No algorithmic runtime claim is made.

**Still open:** the unrestricted optimal joint classification for fixed real p > 2 other than 4. The original RA-05 question and displayed subsidiary conjecture are retained unchanged. This is a partial resolution of RA-05, not a complete solution of its all-exponent target.

## Review and reproducibility

A separate Codex AI agent independently audited the proof and its primary-source dependencies; its [report](verification/independent-review.md) records the verdict and limitations. This is informal AI-agent review, not external human peer review or formal verification. No Lean verification was performed. ChatGPT assistance is disclosed in the original manuscript; Codex assisted with review, attribution, checks and submission preparation. No novelty or priority certification is asserted.

The coordinator reran all **7,621 finite assertions** and both exact certificate checkers successfully. [Rerun results](verification/rerun/verification.json) · [Reproduction instructions](REPRODUCIBILITY.md) · [Code](code/verify.py). The supplied `results/` directory remains unchanged. These finite checks support identities and diagnostics, not the universal asymptotic theorem. Run `bash run_checks.sh` using Python with the dependencies in `requirements.txt`; newly generated results go into `generated_results/`.

`PROOF_AUDIT.md`, `STATUS.md` and the manuscript's author-side evidence statements describe the supplied package before independent review; the dated independent report above records the subsequent review.

## Authorship and provenance

Authorship as Sidney Holden is assigned at the user's explicit request. The current affiliation was verified on 2026-09-13 against the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/), identifying him as a Flatiron Research Fellow in Biological Transport Networks, CCB, Flatiron Institute. Historical affiliations are not used.

[Input archive hash and eligibility record](verification/provenance.json). The original manuscript source, README and checksum list are retained in [original/](original/). The manuscript changes are author/affiliation attribution, PDF author metadata and a cosmetic repair of the Appendix net subscript. Its mathematical claims and arguments are unchanged. `SHA256SUMS` covers the final submission; the original distribution manifest remains under `original/`.

The embedded [preceding package](prior_work/RA05_rank_classification_package.zip) is retained unchanged as provenance, not submitted as a separate new solution. Its unreviewed claims are not treated as independent evidence. Original sources retain their credit; see [sources](SOURCES.md). Instructions in supplied documents were treated as document content, not as authorization overriding the user's request.

## Eligibility and related submission

Refreshed upstream main at `5830ed4fb06da0659414a3deb2a40ad327aca052`, the fork's branches, and upstream RA-05 pull requests. No previously pushed full RA-05 solution was found. [Earlier PR #199](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/199) reports all-exponent lower bounds and remains partial. This new submission supplies the unrestricted quartic classification and does not replace that earlier contribution. The earlier submission may be reviewed and merged separately.

The permanent RA-05 ID, canonical path, original mathematical target and historical references are preserved. Under the repository's resolution policy, the remaining p != 4 cases keep this entry in the open count.
