# MI-03 independent proof review

**Verdict: PASS — complete affirmative resolution of the exact canonical target.**

Review date: 2026-09-11. Reviewer: independent agent `/root/review_matrix_orbits`. Canonical target: `matrix-inequalities-and-norms/MI-03/README.md`. Original read in full: `.cache/colbrook-matrix-submission/nla_submission/proofs/MI-03.tex`; the bundle preamble and bibliography were also read.

## Full original identity

SHA-256: `2d2d0ac01e22de1c6d63471c0965b1c17362d5eda23d53cbf397ab4932be32b3`.

Hash procedure: decode the entire original file as strict UTF-8, replace CRLF by LF, re-encode as UTF-8, and hash, with no extraction, trimming, or other whitespace changes. Original and normalized lengths are both 2,837 bytes; no bare CR occurs. This review attaches to that full TeX identity, not to an extracted proof or independently rendered PDF.

## Target and source alignment

The target quantifies over every square complex dimension and all operator-norm contractions, and asks sharpness of the additive constant k/4 for each odd k at least three. The proof handles every k at least two. A single dimension-two example for each such k suffices for the dimension-independent lower bound. The source gives the same upper bound and separately poses odd-k sharpness after Remark 4.5; neither Hermitian input nor a positive-definite input condition is part of this contraction question. [Bourin–Lee, arXiv v3, Corollary 4.4 and Remark 4.5](https://arxiv.org/html/2307.02034v3#S4).

## Complete proof audit

1. Put R equal to the modulus of the sum and T equal to the sum of individual moduli. The vector Cauchy–Schwarz inequality holds for arbitrary complex vectors A_j x and gives R² ≤ k sum A_j* A_j in ordinary positive-semidefinite order. A contraction has all singular values at most one; functional calculus gives |A_j|² ≤ |A_j|. Thus R²/k ≤ T. Subtracting R and adding kI/4 on both sides is legitimate without commutation of R and T. The resulting lower bound is (R-kI/2)²/k, positive because R is Hermitian. There is no invalid squaring or square-root order inference.

2. Each displayed v_j has norm one; A_j = e_1 v_j* has rank one and operator norm one. Its right Gram matrix is the rank-one projection v_j v_j*, whose positive square root is itself. For k ≥ 2, the complete root-of-unity sum vanishes, including its conjugate. Consequently the sum of A_j is diag(k/2,0), which is already positive. Summing v_j v_j* cancels the off-diagonal entries and gives diag(k/4,3k/4). Their difference has eigenvalues k/4 and -3k/4. Testing e_1 forces any admissible c to be at least k/4. This works for each odd k, not just a subsequence or a limit.

3. In the additional Hermitian construction, w_j is a unit vector orthogonal to e_1. On their two-dimensional span, H_j exchanges e_1 and w_j and has eigenvalues 1 and -1; on the orthogonal complement it is zero. Therefore its norm is one and |H_j| = e_1e_1* + w_jw_j*. The root sums give the two displayed diagonal moduli of the sum and sum of moduli. The e_2 quadratic-form difference is k/4. These are complex Hermitian 3-by-3 matrices; no claim that every odd-k construction is real is needed.

4. The optional positive decomposition is exact: sum over i<j of (A_i-A_j)*(A_i-A_j) equals k sum A_j*A_j minus R². Adding the first term and the squared final term cancels these Gram terms and yields kT-kR+k²I/4. Every summand is positive under the stated contraction condition.

## Scope and limitations

No material gap was found. The infimum is attained by the proved upper bound and matched by exact examples. The excluded k=1 would have optimal constant zero; the manuscript consistently assumes k ≥ 2. Scalar dimension one cannot supply the lower bound, but the target is dimension-independent and includes dimension two. All proof steps were checked algebraically; numerical diagnostics were not used as proof. This is independent agent review, not external human peer review, formal verification, or an exhaustive novelty/priority search. No canonical or original proof edits were made.
