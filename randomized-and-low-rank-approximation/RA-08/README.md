# RA-08 — Concave-function transfer of spectral low-rank error

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because scalar concavity must control noncommuting spectral errors; community impact is reusing low-rank approximations across matrix functions.  
**Topic:** Low-rank approximation of matrix functions.  
**Last checked:** 2026-09-10  
**Status:** Partially resolved  

Let $n\ge2$, $1\le k<n$, and $A,\widehat A\in\mathbb R^{n\times n}$ satisfy $A\succeq\widehat A\succeq0$, where the matrices are symmetric and $\succeq$ is the positive semidefinite ordering. Let $f:[0,\infty)\to[0,\infty)$ be continuous, concave, and nondecreasing.

For $X=\sum_{i=1}^n\lambda_iq_iq_i^T$ with orthonormal $q_i$ and $\lambda_1\ge\cdots\ge\lambda_n\ge0$, set

$$
X_k=\sum_{i=1}^k\lambda_iq_iq_i^T,
\quad f(X)=\sum_{i=1}^nf(\lambda_i)q_iq_i^T,
\quad f(X)_k=\sum_{i=1}^kf(\lambda_i)q_iq_i^T.
$$

Use the same eigenvectors for the two truncations, allowing any choice within repeated eigenspaces. For every $\varepsilon\ge0$, does

$$
\|A-\widehat A_k\|_2\le(1+\varepsilon)\|A-A_k\|_2
$$

imply

$$
\|f(A)-f(\widehat A)_k\|_2\le(1+\varepsilon)\|f(A)-f(A)_k\|_2?
$$

Here $\|\cdot\|_2$ is the spectral norm. The question concerns every such matrix pair, function, and choice of eigendecompositions. It would allow spectral approximation guarantees to pass through a wider family of scalar functions without requiring matrix-vector products with $f(A)$.

## References

1. D. Persson, R. A. Meyer, and C. Musco, [Algorithm-agnostic low-rank approximation of operator monotone matrix functions](https://arxiv.org/html/2311.14023v2), *SIAM Journal on Matrix Analysis and Applications* 46 (2025), 1–21. Table 1, operator-norm/concave/ordered cell, explicitly labels this open; §5 reiterates it. Equation (2) fixes the truncation convention; Theorem 2.7 proves the operator-monotone case.
2. D. Persson, T. Chen, and C. Musco, [Randomized block-Krylov subspace methods for low-rank approximation of matrix functions](https://arxiv.org/abs/2502.01888), *Linear Algebra and its Applications* 741 (2026), 32–65. Abstract and algorithmic error analysis concern specific Krylov approximants rather than this universal implication.

## Status check — 2026-09-08

Checked the first paper's latest listed arXiv v2 (2024-07-04), its 2025 journal record, Table 1, and §5. Searches for the title with “concave”, “counterexample”, “funNyström”, and 2026 found no resolution. The related 2026 Krylov paper was inspected for scope and did not supply this implication. The source's operator-norm counterexample drops the ordering assumption and therefore does not refute the statement here. No explicit reaffirmation later than the 2025 publication was located. The matrix field here follows the source's real symmetric setting, rather than the attachment's broader Hermitian convention.

## Audit — 2026-09-10

Rechecked [Table 1 and Theorem 2.7](https://arxiv.org/html/2311.14023v2): the ordered operator-monotone subclass is proved, but the larger concave class remains open. Concave-transfer and later matrix-function searches found no general resolution. The source's unordered counterexample does not refute this target.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
