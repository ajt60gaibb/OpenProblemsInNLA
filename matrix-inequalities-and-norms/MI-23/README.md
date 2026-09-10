# MI-23 — Corrected generalized geometric-mean product conjecture

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** The four interacting exponents make this corrected conjecture challenging; its immediate consequences concern specialists in matrix means and log-majorization.

## Problem statement

For positive definite $A,B\in\mathbb C^{n\times n}$, real $r$, and $t\in[0,1]$, define
$$
G_{r,t}(A,B)=A^{r/2}(A^{-1/2}BA^{-1/2})^tA^{r/2}.
$$
Is it true, for every $n\ge1$, every such $A,B$, every $p\ge1$, $t\in[0,1]$, and either $r,s\ge1$ or $r,s\le0$, that
$$
\lambda\bigl(G_{r,t}(A,B)^pG_{s,1-t}(A,B)^p\bigr)
\prec_{\log}\lambda\bigl(A^{p(r+s-1)}B^p\bigr)?
$$
The eigenvalues of these products are positive real numbers, ordered decreasingly: each product is similar to a positive definite matrix. For positive decreasing vectors $x,y\in\mathbb R^n$, $x\prec_{\log}y$ means $\prod_{j=1}^kx_j\le\prod_{j=1}^ky_j$ for $1\le k<n$, with equality at $k=n$.

This compares nonlinear matrix-mean products with products of powers of the input matrices. It would give simultaneous multiplicative control for every partial product of ordered eigenvalues and strengthen norm estimates used with positive definite matrix functions.

## References

1. M. M. Ghabries, H. Abbas, B. Mourad and A. Assi, *New log-majorization results concerning eigenvalues and singular values and a complement of a norm inequality*, preprint (2021), Conjecture 2.1, p. 6. [PDF](https://arxiv.org/pdf/2105.13356).
2. M. M. Ghabries, *Contributions to Matrix Inequalities and Some Applications*, PhD thesis, University of Angers and Lebanese University (2022), final Open Problems, Problem 6, pp. 109–110. [Thesis uploaded by its author](https://www.researchgate.net/publication/361793582_Contributions_to_Matrix_Inequalities_and_Some_Applications).
3. M. M. Ghabries, *A log-majorization inequality for normal matrices with applications to determinantal inequalities and geometric means* (2026), §4. [Full text](https://arxiv.org/html/2607.21163).

Status check (2026-09-10): Theorem 2.1 and equation (13) of the first source prove a substantive included region: $r,s\ge1$, $1\le p\le2$, and $\frac{r(p-1)}{(r+s)p}\le t\le\frac{rp+s}{(r+s)p}$. This includes $p=1$ for all $t$. The full parameter range is the remaining question. The first source refutes its earlier unrestricted singular-value Conjecture 1.2; the statement here is the explicitly proposed replacement. The thesis retains it. The July 2026 paper concerns eigenvalue products of ordinary weighted means and does not claim this full $r,s,p$ statement. Current arXiv versions and searches for the authors, “Conjecture 2.1 generalized geometric mean” and 2025/2026 yielded no full resolution. This is a bounded check, not certification of openness.
