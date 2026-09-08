# MI-01 — Audenaert's two-row Schatten norm-compression conjecture

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Last checked:** 2026-09-08

## Problem statement

Let $N,r_1,r_2,c_1,\ldots,c_N$ be positive integers and let $A_j\in\mathbb C^{r_1\times c_j}$, $B_j\in\mathbb C^{r_2\times c_j}$. For $1\le p<\infty$, let $\|X\|_p=(\sum_i\sigma_i(X)^p)^{1/p}$, where $\sigma_i(X)$ are the singular values. Define

$$T=\begin{bmatrix}A_1&\cdots&A_N\\B_1&\cdots&B_N\end{bmatrix},\qquad
C_p(T)=\begin{bmatrix}\|A_1\|_p&\cdots&\|A_N\|_p\\\|B_1\|_p&\cdots&\|B_N\|_p\end{bmatrix}.$$

Do the following inequalities hold for every such partition?

$$\|T\|_p\ge\|C_p(T)\|_p\quad(1\le p\le2),\qquad
\|T\|_p\le\|C_p(T)\|_p\quad(2\le p<\infty).$$

## Why it matters

The question asks whether the norm of a large block matrix can be controlled sharply using only the norms of its blocks. Such compression estimates are useful when analyzing matrix approximation errors without retaining the full matrices.

## References

1. K. M. R. Audenaert, *On a norm compression inequality for $2\times N$ partitioned block matrices*, arXiv:math/0702186v2 (26 March 2007), Conjecture 1, equations (1)–(2), §§2 and 4. Published in Linear Algebra and its Applications 428(4) (2008). [Primary text](https://arxiv.org/html/math/0702186).
2. T. Zhang, *Clarkson–McCarthy type inequalities, part I: $\ell_p$–$\ell_p$ and $\ell_q$–$\ell_p$ Schatten $p$-estimates*.  
   arXiv:2410.21961v4 (28 March 2026), Conjecture 1.14 and Theorem 1.15. [Primary text](https://arxiv.org/html/2410.21961).

## Status check — 2026-09-08

The 2026 revision still states this conjecture and supplies a weaker bound. Audenaert proves several restricted cases, including $p\ge4$; the three-row generalization has counterexamples. Hanner's inequality, a special case, has subsequently been proved, which does not settle arbitrary two-row compression. Searches included `Audenaert norm compression conjecture 2026`, `two row Schatten compression proof`, and `norm compression counterexample 2025 2026`; no general resolution was located. Latest arXiv versions were checked for both references.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
