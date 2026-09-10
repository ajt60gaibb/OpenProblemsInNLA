# RA-09 — Concave-function transfer of Frobenius low-rank error

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because squared Frobenius transfer needs control of eigenvectors as well as eigenvalues; community impact is reusable low-rank approximation of matrix functions.  
**Topic:** Low-rank approximation of matrix functions.  
**Last checked:** 2026-09-10  
**Status:** Partially resolved  

Let $n\ge2$, $1\le k<n$, and $A,\widehat A\in\mathbb R^{n\times n}$ be symmetric with $A\succeq\widehat A\succeq0$. Let $f:[0,\infty)\to[0,\infty)$ be continuous, concave, and nondecreasing. For a positive semidefinite matrix $X=\sum_{i=1}^n\lambda_iq_iq_i^T$ with decreasing eigenvalues and orthonormal eigenvectors, write

$$
X_k=\sum_{i=1}^k\lambda_iq_iq_i^T,
\quad f(X)=\sum_{i=1}^nf(\lambda_i)q_iq_i^T,
\quad f(X)_k=\sum_{i=1}^kf(\lambda_i)q_iq_i^T.
$$

Use the same eigenvectors for the two truncations, with any choices inside repeated eigenspaces. Is the implication

$$
\|A\|_F^2-\|\widehat A_k\|_F^2
\le(1+\varepsilon)\|A-A_k\|_F^2
$$

$$
\Longrightarrow\quad
\|f(A)-f(\widehat A)_k\|_F^2
\le(1+\varepsilon)\|f(A)-f(A)_k\|_F^2
$$

valid for every such input, every eigendecomposition choice, and every $\varepsilon\ge0$? Here $\|M\|_F^2=\sum_{i,j}|M_{ij}|^2$. The premise is intentionally the difference of squared norms, not merely a relative-error bound for $\widehat A_k$.

The problem asks whether a reusable approximation to $A$ provides near-optimal Frobenius approximation to a larger class of matrix functions.

## References

1. D. Persson, R. A. Meyer, and C. Musco, [Algorithm-agnostic low-rank approximation of operator monotone matrix functions](https://arxiv.org/html/2311.14023v2), *SIAM Journal on Matrix Analysis and Applications* 46 (2025), 1–21. Table 1, Frobenius/concave/ordered cell and its asterisk; Theorem 2.5 supplies the stronger premise being extended, and §5 explicitly leaves the concave case open. Equation (2) specifies truncation.
2. D. Persson, T. Chen, and C. Musco, [Randomized block-Krylov subspace methods for low-rank approximation of matrix functions](https://arxiv.org/abs/2502.01888), *Linear Algebra and its Applications* 741 (2026), 32–65. This related work analyzes particular randomized Krylov constructions.

## Status check — 2026-09-08

Checked the source's latest listed arXiv v2 (2024-07-04), 2025 journal record, Table 1, Theorem 2.5, and §5. Searches combining the title, “concave”, “Frobenius”, “counterexample”, “funNyström”, and 2026 found no resolution. The related 2026 Krylov paper does not establish the universal ordered-pair implication. No explicit reaffirmation later than the 2025 publication was located. The source's nuclear-norm counterexample and its unordered Frobenius example do not answer this target. Unlike the spectral-error question, this statement concerns squared Frobenius error and a stronger premise; these are distinct explicitly marked open cells in the source table.

## Audit — 2026-09-10

Rechecked [Table 1 and Theorem 2.5](https://arxiv.org/html/2311.14023v2): operator-monotone functions satisfy this stronger-premise implication, while general concave functions remain open. Frobenius/concavity and later matrix-function searches found no resolution. The difference-of-squared-norms premise is essential.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
