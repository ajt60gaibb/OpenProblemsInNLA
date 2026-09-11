# Sharp random-pivoting bounds — Matthew J. Colbrook, 11 September 2026

**Author:** Matthew J. Colbrook. **Affiliation:** Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom. **Email:** m.colbrook@damtp.cam.ac.uk. [Official affiliation](https://www.damtp.cam.ac.uk/user/mjc249/home.html), checked 11 September 2026.

This submission processes only RA-02 and RA-03 from `nla_RA02_RA03_submission_review_pending.zip`. Authorship is added at the submitter's request. AI assistance is disclosed; independent agent review is not external human peer review or formal certification, and no historical priority claim is made.

## Eligibility and the original hold

The supplied archive marked its drafts HOLD because its repository access had failed. That is a historical limitation, preserved in [the original README](submitted/README.md) and audit. The [live eligibility audit](verification/eligibility-live.json) checks both canonical pages on every one of 25 public upstream/fork branches (50 page checks): all were Open. All public issue/PR bodies, review and discussion comments, and PR changed-file records showed no RA-02 or RA-03 full-solution claim or solution awaiting review, including omnibus PRs #6 and #32. Accordingly neither target duplicates one of our pushed full solutions or a listed pending resolution. Private or unpublished work cannot be excluded.

## Exact resolutions

### RA-02: Sharp exponential factor for same-rank randomly pivoted Cholesky

Theorem 1 and Corollary 3 disprove the existence of constants $C,p$ giving the displayed polynomial bound after exactly $r$ pivots. For every fixed $r\ge1$, real entrywise-positive positive-definite matrices of order $r+1$ approach the sharp expected trace-error ratio $2^r$ as a parameter tends to zero. Choose $r$ first and then the parameter; no limit uniform in $r$ is needed. The result does not address oversampling (RA-01).

[Canonical page](../../randomized-and-low-rank-approximation/RA-02/README.md) · [Independent review](verification/reviews/RA-02-review.md).

### RA-03: Sharp exponential squared-error factor for randomly pivoted LU

Section 2 gives the exact counterexample $A=\left(\begin{smallmatrix}2&1\\1&2\end{smallmatrix}\right)$: one pivot has expected squared Frobenius error $18/5$, while the best rank-one squared error is $1$. Thus the displayed $2^k$ bound is false already at $k=1$. Theorem 1 additionally proves that the known $4^r$ factor is sharp as a supremum at every rank, even on real entrywise-positive positive-definite inputs.

[Canonical page](../../randomized-and-low-rank-approximation/RA-03/README.md) · [Independent review](verification/reviews/RA-03-review.md).

## Complete proof and provenance

[Authored manuscript PDF](manuscripts/sharp_random_pivoting.pdf) · [standalone TeX](manuscripts/sharp_random_pivoting.tex) · [original source](submitted/manuscript/sharp_random_pivoting.tex). The entire mathematical body from the abstract through the bibliography is unchanged. Author/affiliation/date, review disclosure and minor front-matter typesetting are added before that body. The original statements about failed repository access are historical; the live audit above resolves that submission prerequisite.

Both complete-source proof reviews bind the same normalized UTF-8/LF SHA256. They check the fixed-rank asymptotics, all pivot-history probabilities, spectral-tail scaling and the separate unit-diagonal replication extension. The simpler RA-03 counterexample independently suffices for its canonical target. The sharp-factor lower examples are deliberately ill-conditioned; no practical average-case, bounded-condition-number or oversampling assertion is made.

All 30 archive files are retained unchanged under `submitted/`; all 29 supplied checksum entries pass. The [archive manifest](verification/archive-manifest.json) records their byte hashes and the ZIP hash. The archived drafts are preserved evidence, not instructions executed automatically.

## Exact verification and documents

[Computational review](verification/reviews/computational-review.md) and [fresh outputs](verification/rerun/) record the full standard-library exact rational suite, complete small-rank pivot enumeration, rank-eight retained-history certificate, replication checks and the 2-by-2 counterexample. These finite checks supplement the parameter-uniform proof; the rank-eight example alone cannot refute every polynomial factor.

For reproduction, copy `submitted/verification/` to a scratch directory and run its `test_suite.py` and the documented scripts, keeping original evidence untouched. The original command for `verify_ra03_2x2.py --out` is inaccurate: that script prints JSON and has no argument parser; capture stdout into the desired JSON file instead. This packaging issue has no mathematical effect.

Run `python verification/build_manuscript.py` with XeLaTeX installed (or set `XELATEX`) to rebuild the attributed PDF. The builder checks both full-source review hashes and exact mathematical-body preservation. Canonical Markdown/TeX/PDF, RESOLVED and catalog changes are included together. [Final document/safeguard checks](verification/document-checks.json) record validation and visual inspection.
