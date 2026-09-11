# IE-13 — Sharp growth for unequal lower and upper bandwidths

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved
**Last checked:** 2026-09-11

<!-- colbrook-recovered -->
## Independently reviewed resolution - 2026-09-11

**Sharp growth classification.** Theorem 1 and Sections 2-4 prove $G(0,q)=1$ and $G(p,q)=h_{p+q}$ for $p\ge1$, where $h_t=0$ for $t\le0$ and $h_t=1+\sum_{r=1}^p h_{t-r}$ otherwise. The upper bound covers every complex input and admissible tie path, with growth over all active entries in the fixed original ordering. A real nonsingular matrix of order $2p+q+1$ attains it, including zero upper bandwidth.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](../../references/colbrook-recovered-2026-09-11/manuscripts/IE-13.pdf), [independent proof review](../../references/colbrook-recovered-2026-09-11/verification/reviews/IE-13-review.md), and [submission record](../../references/colbrook-recovered-2026-09-11/README.md). The supplied notes were reconstructed with substantial AI assistance. This is independent agent verification, not external human peer review or formal proof-assistant certification; no novelty or priority claim is made.

The difficulty, importance and rating rationale below are historical assessments of the original open target. Original statements, references and dated audits are preserved.
<!-- /colbrook-recovered -->

**Rating rationale:** Challenging reflects interacting fill-in and pivot choices across arbitrary unequal bandwidths; specialist impact is a sharp stability classification for banded elimination.

## Problem statement

Work in exact arithmetic over $\mathbb C$. For integers $p,q\ge0$, define

$$
\mathcal B_n(p,q)=\{A\in\mathbb C^{n\times n}:\det A\ne0,\quad
a_{ij}=0\text{ if }i-j>p\text{ or }j-i>q\}.
$$

Gaussian elimination with partial pivoting (GEPP) chooses a largest-modulus entry in the active first column, moves its row to the first position, and forms the trailing Schur complement. For a permitted path $\pi$, let $S_1=A,\ldots,S_n$ be its active matrices and define

$$
\rho(A,\pi)=\frac{\max_{1\le k\le n}\|S_k\|_{\max}}{\|A\|_{\max}},
\qquad \|M\|_{\max}=\max_{i,j}|m_{ij}|.
$$

Determine, for all $p\ne q$, the sharp bound independent of dimension,

$$
G(p,q)=\sup_{n\ge1+\max(p,q)}\ \sup_{A\in\mathcal B_n(p,q)}\
\sup_{\pi\text{ permitted by GEPP}}\rho(A,\pi).
$$

Identify the least universal upper bound and matching examples approaching it. All tie choices are included. The bandwidth restrictions apply in the given ordering; no reordering before GEPP is allowed. Bandwidths are *at most* $p$ and $q$; unequal pairs with one zero bandwidth are included. For $p\ge1$, the equal-bandwidth case is known:

$$G(p,p)=2^{2p-1}-(p-1)2^{p-2}.$$

This asks how unequal bandwidths affect worst-case element growth in banded linear solves. All unequal pairs constitute one problem.

## References

N. J. Higham, [*Accuracy and Stability of Numerical Algorithms*, second edition](https://doi.org/10.1137/1.9780898718027), SIAM (2002), Problem 9.15(a), p. 193; definitions and Theorem 9.11, pp. 172–173. Z. Bohte, [*Bounds for Rounding Errors in the Gaussian Elimination for Band Systems*](https://doi.org/10.1093/imamat/16.2.133), J. Inst. Maths. Applics. 16 (1975), 133–142.

## Earlier status check — 2026-09-08

The book's problem was checked directly. Its wording omits the field; this entry adopts $\mathbb C$ from its referenced Theorem 9.11. Searches for `Higham 9.15 growth`, `growth factor lower bandwidth upper bandwidth`, and `Bohte Gaussian 1975` found no general unequal-bandwidth solution. Shah–Urschel's [August 31, 2026 revision](https://arxiv.org/html/2608.19189v4), Theorems 2.2–2.3, studies sparsity constraints without determining this extremal function. No recent explicit reaffirmation of this particular question's openness was located; the status rests on the original question and this bounded later-literature check.

## Audit update — 2026-09-10

Higham's [Problem 9.15(a)](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf), p. 193, remains the explicit historical source. Unequal-bandwidth and sharp-growth searches, including the [August 2026 complete-pivoting manuscript](https://arxiv.org/html/2608.19189v4), did not identify a sharp answer for this partial-pivoting sparsity pattern. This is a bounded historical-source assessment, without a recent explicit reaffirmation.
