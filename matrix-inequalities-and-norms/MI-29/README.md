# MI-29 — Modulus-order determinant comparison with an arbitrary base power

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Arbitrary base powers and indefinite Hermitian factors make extension of the squared-base theorem challenging; the comparison has specialist importance for determinant inequalities.

## Problem statement

Does the inequality
$$
\det(A^k+|AB|^p)\ge\det(A^k+|BA|^p)
$$
hold for every integer $n\ge1$, every positive definite $A\in\mathbb C^{n\times n}$, every invertible Hermitian $B\in\mathbb C^{n\times n}$, and every pair of real parameters $k,p\ge0$? Here $|X|=(X^*X)^{1/2}$, all powers of positive definite matrices use spectral functional calculus, and $X^0=I$.

Both determinants are positive real numbers. The same conjecture is stated for semidefinite $A$ and Hermitian $B$ in the source; invertible inputs avoid zeroth-power conventions, while the positive-exponent singular cases follow by continuous approximation. No commutation between $A$ and $B$ is assumed.

The two moduli have the same singular spectrum, but adding $A^k$ tests their alignment with the eigenvectors of the base matrix. The question therefore concerns how spectral data and eigenvector geometry interact in determinant estimates for matrix functions.

## References

1. M. M. Ghabries, *Contributions to Matrix Inequalities and Some Applications*, PhD thesis, University of Angers and Lebanese University (2022), §2.5 and final Open Problems, Problem 2, pp. 109–110. [Thesis uploaded by its author](https://www.researchgate.net/publication/361793582_Contributions_to_Matrix_Inequalities_and_Some_Applications).
2. M. M. Ghabries, H. Abbas and B. Mourad, *On some open questions concerning determinantal inequalities*, Linear Algebra Appl. 596 (2020), 169–183, resolution of the earlier $k=2$ question. [Publisher](https://doi.org/10.1016/j.laa.2020.03.009).
3. M. M. Ghabries, *A log-majorization inequality for normal matrices with applications to determinantal inequalities and geometric means*, arXiv:2607.21163v1 (2026), §3. [Full text](https://arxiv.org/html/2607.21163).

Status check (2026-09-10): the thesis states the full question after proving $k=2$ for all $p\ge0$, and further cases when both matrices are positive semidefinite. The July 2026 paper extends the known squared-base result to normal matrices, but does not claim arbitrary $k$ here. Searches for the exact titles, “modulus determinant arbitrary power conjecture Ghabries”, and 2025/2026 found no complete resolution. The negative-power companion in the thesis is not counted separately.
