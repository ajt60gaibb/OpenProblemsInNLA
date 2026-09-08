# IE-15 — Exact small-order growth factors for rook pivoting

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** open in the historical source; no exact resolution found in the bounded later search below.  
**Last checked:** 2026-09-08  

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

## Status check

The book's question and real-field supremum were checked directly. Searches for `rook pivoting 3x3`, `rook pivoting 2.9`, `rook pivoting 4.16`, and `rook pivoting maximum growth exact value` found no exact small-order solution. The cited 2024 large-order construction and 2026 asymptotic result do not settle this pair. The book's decimals 2.9 and 4.16 are historical numerical search outcomes, not exact values. No recent source explicitly reaffirming this particular question's openness was located.
