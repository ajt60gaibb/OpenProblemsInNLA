# NM-04 — The Rowland–Wu polynomial identity for Sinkhorn limits

**Topic:** Exact matrix scaling and balancing.  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Last checked:** 2026-09-08

## Problem statement

Let $m,n\ge1$ and $A\in\mathbb R_{>0}^{m\times n}$. Let $\operatorname{Sink}(A)$ be its Sinkhorn limit with row sums $1$ and column sums $m/n$: equivalently, the unique matrix $D_1AD_2$ with these sums, where $D_1,D_2$ are positive diagonal matrices. Set $x=\operatorname{Sink}(A)_{11}$.

Define

$$
\mathcal D=\{(R,C):R\subseteq\{2,\ldots,m\},\ C\subseteq\{2,\ldots,n\},\ |R|=|C|\}.
$$

Submatrix indices are in increasing order; empty determinants and products equal $1$. Put

$$
\Delta(R,C)=\det A_{\{1\}\cup R,\{1\}\cup C},\qquad
\Gamma(R,C)=a_{11}\det A_{R,C},
$$

$$
M(\mathcal S)=\prod_{(R,C)\in\mathcal S}\Delta(R,C)
\prod_{(R,C)\in\mathcal D\setminus\mathcal S}\Gamma(R,C).
$$

For a finite set $U$ of integers and $s\in U$, let $p_s(U)$ be the position of $s$ in the increasing list of $U$, starting at $1$. For each $\mathcal S=\{(R_i,C_i):1\le i\le k\}\subseteq\mathcal D$, define $H_{\mathcal S}\in\mathbb Z^{k\times k}$ by

$$
(H_{\mathcal S})_{ii}=|R_i|(m+n)-mn,
\qquad
\tau_{ij}=(R_i\setminus R_j,R_j\setminus R_i,C_i\setminus C_j,C_j\setminus C_i),
$$

and, for $i\ne j$,

$$
(H_{\mathcal S})_{ij}=\begin{cases}
(-1)^{p_s(R_j)+p_t(C_j)}m,&\tau_{ij}=(\varnothing,\{s\},\varnothing,\{t\}),\\
(-1)^{p_s(R_i)+p_t(C_i)+1}n,&\tau_{ij}=(\{s\},\varnothing,\{t\},\varnothing),\\
(-1)^{p_s(C_i)+p_t(C_j)}m,&\tau_{ij}=(\varnothing,\varnothing,\{s\},\{t\}),\\
(-1)^{p_s(R_i)+p_t(R_j)}n,&\tau_{ij}=(\{s\},\{t\},\varnothing,\varnothing),\\
0,&\text{otherwise}.
\end{cases}
$$

The determinant is independent of the ordering chosen for $\mathcal S$. Is the following identity valid for every such $A,m,n$?

$$
\sum_{\mathcal S\subseteq\mathcal D}
\det(m^{-1}H_{\mathcal S})M(\mathcal S)x^{|\mathcal S|}=0.
$$

## Why it matters

This would give an explicit algebraic relation for entries of a ubiquitous iterative matrix scaling limit, including a structured formula for every coefficient.

## References

- E. Rowland and J. Wu, [The entries of the Sinkhorn limit of an $m\times n$ matrix](https://arxiv.org/abs/2409.02789), arXiv v2 (2025-05-25), notation on pp. 3–4 and Conjecture 2. The matrix denoted $H_{\mathcal S}$ here is their $\operatorname{adj}_{\mathcal S}(m,n)$.
- E. Rowland, [Combinatorial structure behind Sinkhorn limits](https://ericrowland.github.io/talks/Combinatorial_structure_behind_Sinkhorn_limits_SIAM.pdf), SIAM talk, 2025-07-07, slide 13: the coefficient formula remains conjectural after the degree bound was proved.
- M. C. Fang, [Closed Form of a Generalized Sinkhorn Limit](https://arxiv.org/abs/2506.06338), 2025, abstract and the general algebraic degree bound. This settles the degree-bound consequence, rather than the displayed coefficient formula.

## Status check

On 2026-09-08, checked the latest listed Rowland–Wu arXiv version, Rowland's July 2025 slides, and Fang's 2025 abstract. Searches combined “Sinkhorn”, “Rowland”, “Wu”, “Conjecture 2”, “formula”, “proof”, and 2026. No proof or counterexample to the full displayed identity was located. The degree bound $\binom{m+n-2}{m-1}$ alone has been resolved and is excluded as a separate open problem. The present target retains all coefficients, signs, and the rectangular normalization from the source.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
