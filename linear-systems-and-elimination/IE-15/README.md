# IE-15 — Exact small-order growth factors for rook pivoting

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** hard  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11  

**Rating rationale (historical):** Hard reflects two focused finite-dimensional extremal constants within an established pivoting model; specialist impact concerns exact small-order rook-pivoting behavior.

## Resolution — 2026-09-11

**Solved (affirmative exact values): $g_{\mathrm{RP}}(3)=3$ and $g_{\mathrm{RP}}(4)=14/3$.** George Stepaniants's [complete proof](solution.md), **Theorem 1 and Sections 1–5**, gives universal upper bounds and explicit rational matrices attaining both values. It covers real nonsingular matrices, every admissible rook path, all ties, and every intermediate active entry. [Proof PDF](solution.pdf) · [Standalone TeX](solution.tex).

The complete argument passed an [independent Codex-agent review](../../references/stepaniants-ie15-2026-09-11/verification/reviews/IE-15-review.md), including a separate analytic check of its central scalar inequality and exact rational witness checks. It was developed with ChatGPT/Codex; verification is independent agent review, not external human peer review or formal certification. [Authorship, scope, reproduction and branch check](../../references/stepaniants-ie15-2026-09-11/README.md). The original statement, ID, path, historical ratings and earlier audits below are retained.

<!-- colbrook-recovered -->
## Related order-five bound - 2026-09-11

Matthew J. Colbrook submitted a recovered rational $5\times5$ matrix with an admissible rook path of growth $893/131$. The [complete construction](../../references/colbrook-recovered-2026-09-11/submitted/research/rook_partial.md), [exact rerun](../../references/colbrook-recovered-2026-09-11/verification/fresh-rook-results.json), and [independent review](../../references/colbrook-recovered-2026-09-11/verification/reviews/rook-review.md) verify this finite lower bound, with ties allowed. This order-five note alone did not determine either requested order-three or order-four constant. The complete resolution above now settles both constants; the order-five construction is retained as a separate related result. See the [submission record](../../references/colbrook-recovered-2026-09-11/README.md) for the Cambridge affiliation, AI-assistance disclosure and verification limits.
<!-- /colbrook-recovered -->

## Problem statement

All arithmetic is exact and matrices are real and nonsingular. At each step of Gaussian elimination with rook pivoting, select a nonzero entry maximal in absolute value both in its row and in its column of the active matrix. Move it to the active $(1,1)$ position by row and column interchanges, and form the trailing Schur complement.

For an admissible path $\pi$ on $A\in\mathbb R^{n\times n}$, let $S_1=A,\ldots,S_n$ be the active matrices and define

$$
\rho(A,\pi)=\frac{\max_{1\le k\le n}\|S_k\|_{\max}}{\|A\|_{\max}},
\qquad \|M\|_{\max}=\max_{i,j}|m_{ij}|,
$$
$$
g_{\mathrm{RP}}(n)=\sup_{\substack{A\in\mathbb R^{n\times n}\\\det A\ne0}}\
\sup_{\pi\text{ permitted by rook pivoting}}\rho(A,\pi).
$$

Determine the two exact constants $g_{\mathrm{RP}}(3)$ and $g_{\mathrm{RP}}(4)$, with matching upper and lower bounds. All admissible rook choices and ties are included. The source singles out dimensions at most four; $g_{\mathrm{RP}}(1)=1$ and $g_{\mathrm{RP}}(2)=2$ are known. The two unknown constants are counted as one problem.

Rook pivoting balances pivot-search cost and growth control. Sharp small-order constants would sharpen its finite-dimensional stability theory. General asymptotic growth estimates do not determine them; IE-11 concerns a different pivoting rule.

## References

N. J. Higham, [*Accuracy and Stability of Numerical Algorithms*, second edition](https://doi.org/10.1137/1.9780898718027), SIAM (2002), Problem 9.18, p. 193, and definition (9.15), p. 169. A. Edelman and J. Urschel, [*Some New Results on the Maximum Growth Factor in Gaussian Elimination*](https://doi.org/10.1137/23M1571903), SIMAX 45 (2024), [§6](https://arxiv.org/html/2303.04892v4). R. Shah and J. Urschel, [*Entry growth in Gaussian elimination*](https://arxiv.org/html/2608.19189v4), August 31, 2026 revision, Theorem 1.6 (=6.2).

## Earlier status check — 2026-09-08

The book's question and real-field supremum were checked directly. Searches for `rook pivoting 3x3`, `rook pivoting 2.9`, `rook pivoting 4.16`, and `rook pivoting maximum growth exact value` found no exact small-order solution. The cited 2024 large-order construction and 2026 asymptotic result do not settle this pair. The book's decimals 2.9 and 4.16 are historical numerical search outcomes, not exact values. No recent source explicitly reaffirming this particular question's openness was located.

## Audit update — 2026-09-10

Rechecked Higham's [Problem 9.18](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf), p. 193. Searches for exact order-three/order-four rook growth and the [2026 general pivoting bounds](https://arxiv.org/html/2608.19189v4) found no exact values. Difficulty is reduced to hard to reflect the focused finite-order target, although the global upper-bound proofs may still be substantial. The open verdict remains bounded by a historical explicit source.
