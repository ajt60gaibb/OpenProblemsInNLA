# MI-14 — The complex Lu–Wenzel spectral conjecture

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Provenance:** explicit conjecture  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Uniform control of the full commutator spectrum is a major strengthening of established norm bounds; it connects Sylvester operators with geometric matrix inequalities.

## Problem statement

For every integer $n\ge2$ and $X\in\mathbb C^{n\times n}$ with $\|X\|_F=1$, consider the complex-linear operator

$$T_X:\mathbb C^{n\times n}\longrightarrow\mathbb C^{n\times n},
\qquad T_X(Y)=[X^*,[X,Y]],\qquad [P,Q]=PQ-QP.$$

Use the inner product $\langle Y,Z\rangle_F=\operatorname{tr}(Y^*Z)$. The operator is Hermitian positive semidefinite; list its $n^2$ eigenvalues, including multiplicities, as $\lambda_1(T_X)\ge\cdots\ge\lambda_{n^2}(T_X)\ge0$. Is

$$\sum_{i=1}^{2k}\lambda_i(T_X)\le 2k+2
\qquad\text{for every integer }1\le k\le\lfloor n^2/2\rfloor?$$

## Relevance

This bounds sums of squared singular values of the commutator map $Y\mapsto XY-YX$. Such a map is a basic Sylvester operator. The conjecture strengthens a bound on its largest singular value to simultaneous bounds on its singular spectrum.

## References

1. J. Ge, F. Li, Z. Lu, and Y. Zhou, *On some conjectures by Lu and Wenzel*, arXiv:1908.06624v1, Conjecture 7; Theorems 1.1–1.2 and §4. [Primary manuscript](https://arxiv.org/html/1908.06624v1).
2. J. Ge, F. Li, Z. Tang, and Y. Zhou, *A survey on the DDVV-type inequalities*, Advances in Mathematics (China) 53 (2024), 449–467: published Conjecture 4.6 and Theorems 4.1–4.2, pp.463–464. These are Conjecture 4.14 and Theorems 4.17–4.18 in [arXiv:2402.01085v1](https://arxiv.org/html/2402.01085v1). [Published PDF](https://ccj.pku.edu.cn/Article/DownLoad?id=374327987&type=ArticleFile).
3. Z. Liu, *The Lu–Wenzel Spectral Conjecture for Square-Zero Matrices*, Zenodo record 21693383, abstract. [Author's preprint record](https://zenodo.org/records/21693383).

## Status check — 2026-09-10

Both arXiv sources remain v1. The published survey retains the conjecture and records the normal, rank-one, and $n=2,3$ cases. Liu's record claims the additional class $X^2=0$ and scalar translates; its abstract does not claim the unrestricted assertion. That record's displayed publication date and July 2026 creation metadata differ, so no priority date is inferred from it. Searches used `Lu-Wenzel conjecture proof 2026`, `Lu Wenzel conjecture solved`, and `Lu-Wenzel spectral conjecture`. No general resolution was located. Equivalent majorization and fundamental-commutator formulations, and the real restriction, are grouped in this entry.

**Audit update (2026-09-10):** Rechecked the 2024 survey’s Conjecture 4.14 and special-case discussion, and searched for later Lu–Wenzel spectral results. The normal, rank-one and low-order cases are within the displayed target; the square-zero preprint claims only another restricted class. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
