# Sharp worst-case factors for randomly pivoted Cholesky and LU

**Two proposed negative resolutions: RA-02 and RA-03. Submission status: HOLD — the repository exclusion audit is incomplete.**

The mathematical results below have full proofs and exact-arithmetic verification. They are not represented as accepted repository resolutions, independently peer-reviewed results, or cleared submissions. No issue, pull request, commit, or other public change has been made.

## Results

For every fixed integer `r >= 1`, the manuscript constructs real, entrywise-positive, positive-definite matrices of order `r + 1` for which, after exactly `r` pivots,

\[
\frac{\mathbb E\,\operatorname{tr} R_r}{\sum_{j>r}\lambda_j(A)}\longrightarrow 2^r,
\qquad
\frac{\mathbb E\|B_r\|_F^2}{\|A-A_r^{\rm best}\|_F^2}\longrightarrow 4^r.
\]

The known upper bounds match these limits. Thus the worst-case factors are exactly `2^r` and `4^r`, as suprema. A polynomial-in-`r` same-rank RPCholesky factor is impossible. For RPLU, neither `2^r` nor any fixed polynomial multiple of `2^r` is a uniform squared-error factor. The same suprema hold for positive-definite, entrywise-positive, unit-diagonal matrices when arbitrary dimensions are allowed; a separate replication argument establishes that extension.

The explicit family is `A = L D L^T`, where `n = r + 1`, `L_ii = 1`, `L_ij = t^j/(i+j)` for one-based indices `i > j`, `epsilon = t^(n^2)`, and `D = diag(1, epsilon, ..., epsilon^r)`. The proof first fixes `r` and then lets `t` decrease to zero.

RA-03 also has a stand-alone `2 x 2` rational counterexample: `A = [[2,1],[1,2]]`. The best rank-one squared Frobenius error is `1`, whereas one RPLU step has expected squared error `18/5 > 2`.

## Read first

The main proof is [manuscript/sharp_random_pivoting.pdf](manuscript/sharp_random_pivoting.pdf), with editable LaTeX beside it. Separate issue-body drafts are in [RA-02/submission.md](RA-02/submission.md) and [RA-03/submission.md](RA-03/submission.md). Both are explicitly held for preflight, not authorized for automatic posting.

[verification/README.md](verification/README.md) explains the exact rational checks and the stored results. [review_checklist.md](review_checklist.md) separates completed self-checks from outstanding review. [SOURCES.md](SOURCES.md) identifies the primary mathematical sources.

## Repository eligibility remains unresolved

The retrieved RA issue listing identified existing solution or partial-solution submissions for RA-07, RA-08, RA-09, RA-10, RA-12, and RA-13; those problems were excluded. The retrieved listing did not display a matching RA-02 or RA-03 solution, but this is **not a complete absence check**.

Later GitHub reads failed. In particular, the exact RA-02 and RA-03 `problem.tex` files and the contents/files of omnibus merged pull requests **#6 and #32** were not obtained. These gaps prevent certification that either proposed submission satisfies the instruction to avoid problems with solutions already listed in issues or pull requests. The category-level descriptions and the RPLU paper's explicit conjecture were available; the mathematical theorems in this package are fully specified independently of the repository labels.

See [audit/eligibility.md](audit/eligibility.md) and [audit/eligibility.json](audit/eligibility.json). The read-only script [audit/recheck_github.py](audit/recheck_github.py) collects all issue states, comments, PR review bodies, and changed-file records for human review when GitHub access is available. It never determines eligibility automatically and never changes GitHub. The session's failed API read is preserved in `audit/session_fetch_attempt/report.json`.

**Do not post either draft until the exact current statements and the complete existing-solution history have been checked.** A listed prior solution is grounds to withdraw the corresponding draft, not to relabel this package as the first resolution.

## Reproduce

Python 3.10 or newer is sufficient; all mathematical verification uses the standard library, including `fractions.Fraction`. There are no third-party Python dependencies and no network access is needed for these checks.

```sh
cd verification
python test_suite.py
python verify_ra03_2x2.py --out results/ra03_2x2.json
python exact_enumeration.py --r 3 --t 1/100 --out results/enumeration_r3.json
python exact_certificate.py --r 8 --t 1/100 --out results/exact_r8.json
python verify_replication.py --out results/replication.json
```

The saved regression run passes **10 mathematical tests**, including regeneration of the rank-eight certificate. A separate offline audit-safeguard suite passes **5 tests**; those tests do not constitute a repository audit.

To rebuild the PDF, run `sh build_pdf.sh` from this directory with a standard LaTeX installation containing `pdflatex` and the packages named in the source. To verify archive integrity, run `sha256sum -c SHA256SUMS` before changing or regenerating any files. Regenerated result files contain elapsed timings, so their byte hashes may change even when all exact mathematical fields agree.

## Scope

These are same-rank results: `r` pivots versus the optimal rank-`r` error. They do not resolve RA-01's oversampling question. The small-dimensional family is recovered exactly after `r + 1` pivots. The examples are deliberately ill-conditioned; ordinary floating-point experiments are not a substitute for the exact certificates. No bounded-condition-number or practical average-case claim is made.

The proof and code were developed and self-checked in this research session. Independent mathematical review, a complete novelty check, repository eligibility clearance, author/submitter attribution, and public submission remain outstanding.
