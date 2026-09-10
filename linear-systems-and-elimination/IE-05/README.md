# IE-05 — Exact extremizers for partial pivoting on orthogonal matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Open  
**Last checked:** 2026-09-10  

**Rating rationale:** Challenging reflects a global extremal problem with pivot-path constraints in every dimension; specialist impact concerns sharp constants on the orthogonal subclass.

## Context and notation

All elimination in this problem is in exact arithmetic. Write $\|A\|_{\max}=\max_{ij}|a_{ij}|$. A pivoting path creates successive active Schur complements $S_1=A,S_2,\ldots,S_n$, with row/column permutations as appropriate. Its element-growth factor is

$$
\rho(A)=\frac{\max_{1\leq j\leq n}\|S_j\|_{\max}}{\|A\|_{\max}}.
$$

Partial pivoting chooses a largest-magnitude entry in the active first column; complete pivoting chooses one anywhere in the active matrix. If ties occur, a universal statement includes every admissible tie choice; a supremum includes all admissible paths. These conventions remove implementation-dependent ambiguity. Matrices are nonsingular unless otherwise stated.

## Problem statement

Let $L_n$ be the real unit lower triangular matrix whose entries strictly below the diagonal are all $-1$. Define $Q_n$ by the unique QR factorization $L_n=Q_nR_n$ with positive diagonal in $R_n$. For $Q_n$, use partial pivoting with the first available row chosen in a tie. Is it true that, for every $n\geq2$,

$$
\sup_{Q\in O(n)}\rho_{\mathrm{PP}}(Q)
=\rho_{\mathrm{PP}}(Q_n),
\qquad O(n)=\{Q\in\mathbb R^{n\times n}:Q^TQ=I\}?
$$

The supremum on the left includes all admissible partial-pivoting paths. The candidate is fully specified by $L_n$, rather than by an approximate numerical optimizer. This asks for the sharp extremizer, beyond the established exponential order of orthogonal growth.

## Reference

Peca-Medlin, [*Growth factors of orthogonal matrices and local behavior of Gaussian elimination with partial and complete pivoting*](https://arxiv.org/html/2308.16146v2), published in SIAM J. Matrix Anal. Appl. (2024), §3.2 and Appendix B. The paper conjectures this equality and establishes $\rho_{\mathrm{PP}}(Q_n)=2^{n-1}(1+o(1))/\sqrt3$.

## Earlier status check — 2026-09-08

Searches for `GEPP orthogonal conjecture 2026` and the exact paper title found no proof of the extremal equality. The 2026 butterfly paper still identifies orthogonal partial-pivoting growth as open. The August Shah–Urschel results concern different growth questions and pivot strategies; their exponential examples do not establish this exact supremum.

## Audit update — 2026-09-10

Rechecked [Peca-Medlin's manuscript](https://arxiv.org/html/2308.16146v2), §3.2 and Appendix B, and its [SIAM publication](https://doi.org/10.1137/23M1597733), SIAM J. Matrix Anal. Appl. 45 (2024), 1599–1620. The candidate extremizers remain supported by the stated construction and experiments, without a general optimality proof. Searches for subsequent orthogonal GEPP extremizer results found no resolution.
