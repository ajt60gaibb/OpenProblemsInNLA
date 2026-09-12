# RA-18 — The Goreinov–Tyrtyshnikov–Zamarashkin conjecture on square-submatrix inverse norms

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging
**Importance:** interesting to the community
**Status:** Partially resolved
**Last checked:** 2026-09-11

**Rating rationale:** Improving the classical bound is challenging and would sharpen stability guarantees for skeleton/CUR approximation.

## Problem statement

For integers $`1\le r< n`$, let $`U\in\mathbb R^{n\times r}`$ satisfy $`U^TU=I_r`$.
Write $`U_I=U(I,:)`$ for $`I\subseteq\{1,\ldots,n\}`$ with $`|I|=r`$, and let $`\|\cdot\|_2`$ denote the spectral norm.

**Conjecture** (Goreinov–Tyrtyshnikov–Zamarashkin [1, Eq. (2.6)]).
Every such $`U`$ admits a nonsingular square submatrix $`U_I`$ satisfying

```math
\|U_I^{-1}\|_2\le\sqrt n.
```

In the notation of [1], this is $`t(r,n)\le\sqrt n`$, where

```math
t(r,n)=
\max_{\substack{U\in\mathbb R^{n\times r}\\U^TU=I_r}}
\qquad
\min_{\substack{I\subseteq\{1,\ldots,n\}\\|I|=r,\ \det(U_I)\ne0}}
\|U_I^{-1}\|_2.
```

The minimum is over nonsingular submatrices; at least one exists because $`\mathop{\mathrm{rank}}\nolimits(U)=r`$.

## Known bounds and cases

The bound

```math
t(r,n)\le\sqrt{r(n-r)+1}
```

is well known and follows from various arguments: maximal volume [1], Bischof–Stewart QR (BSQR) [2, 3], or volume sampling [4, 5] just to name a few.
Also, $`t(r,n)\ge\sqrt n`$ whenever $`r+1`$ divides $`n`$ [1, Lem. 2.2], so the conjectured constant is sharp.

The real case $`r=1`$ is elementary.
Nesterenko [6] proved the real case $`n=4`$, $`r=2`$; Sengupta–Pautov [7] subsequently proved $`r=2`$ for all $`n`$.
Orthogonal completion gives $`t(r,n)=t(n-r,n)`$, leaving $`3\le r\le n-3`$ as the general open range.
These inverse norms control pseudoskeleton approximation errors [1, Thms. 3.1–3.2].

## Proposed complex extension

Define $`t_{\mathbb C}(r,n)`$ analogously using $`U\in\mathbb C^{n\times r}`$ with $`U^*U=I_r`$, where $`*`$ denotes conjugate transpose.
The minimization again runs only over nonsingular $`U_I`$.
The classical bound $`\sqrt{r(n-r)+1}`$ also holds over $`\mathbb C`$ [3].

**Conjecture (proposed by the contributor).** There is an absolute constant $`\alpha`$, independent of $`r`$ and $`n`$, such that

```math
t_{\mathbb C}(r,n)\le\alpha\sqrt n,
\qquad 1\le r< n.
```

The dependence on $`r,n`$ and the best possible $`\alpha`$ remain to be determined.
The constant $`\alpha=1`$ fails: $`t_{\mathbb C}(2,4)=\sqrt{3+\sqrt3}>2`$ [8, 9].
For two columns, Nesterenko [9, Prop. 1] proves

```math
t_{\mathbb C}(2,n)\le c_2\sqrt n,
\qquad c_2=\left(2-\frac2{\sqrt3}\right)^{-1/2}\approx1.08766,
```

with equality whenever $`4\mid n`$, so any universal $`\alpha`$ must satisfy $`\alpha\ge c_2`$.

## References

1. S. A. Goreinov, E. E. Tyrtyshnikov, and N. L. Zamarashkin, *A theory of pseudoskeleton approximations*, Linear Algebra and its Applications **261** (1997), 1–21.
   [Published paper](https://doi.org/10.1016/S0024-3795(96)00301-1).
2. A. Damle, *Computing Strong Rank-Revealing Factorizations for Matrices with Orthonormal Rows*, arXiv: 2607.13532v1 (2026).
   [Preprint](https://arxiv.org/pdf/2607.13532v1).
3. A. I. Osinsky, *Close to optimal column approximation using a single SVD*, Linear Algebra and its Applications **725** (2025), 359–377.
   [Published paper](https://doi.org/10.1016/j.laa.2025.07.016).
4. H. Avron and C. Boutsidis, *Faster subset selection for matrices and applications*, SIAM Journal on Matrix Analysis and Applications **34** (2013), 1464–1499.
   [Published paper](https://doi.org/10.1137/120867287).
5. A. Cortinovis and D. Kressner, *Adaptive Randomized Pivoting for Column Subset Selection, DEIM, and Low-Rank Approximation*, SIAM Journal on Matrix Analysis and Applications **47** (2026), 25–47.
   [Published paper](https://doi.org/10.1137/24M1719189).
6. Y. Nesterenko, *Submatrices with the best-bounded inverses: revisiting the hypothesis*, arXiv: 2303.07492 (2023; revised 2024).
   [Preprint](https://arxiv.org/abs/2303.07492).
7. R. Sengupta and M. Pautov, *On the submatrices with the best-bounded inverses*, arXiv: 2604.05944v5 (2026).
   [Preprint](https://arxiv.org/html/2604.05944v5).
8. Y. Nesterenko, *Submatrices with the best-bounded inverses: Studying $`\mathbb R^{n\times2}`$ and $`\mathbb C^{n\times2}`$*, arXiv: 2408.16631v1 (2024).
   [Preprint](https://arxiv.org/html/2408.16631v1).
9. Y. Nesterenko, *Submatrices with the best-bounded inverses: an asymptotically tight upper bound for $`\mathbb C^{n\times2}`$*, arXiv: 2604.24087v1 (2026).
   [Preprint](https://arxiv.org/html/2604.24087v1).

## Status check — 2026-09-11

Checked [1]–[9] and searched for later resolutions; no general real-case resolution or resolution of the proposed complex extension was found.
The real two-column result is a preprint and supports the partially resolved status.
