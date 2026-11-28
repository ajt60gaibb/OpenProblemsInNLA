# AC-03 — Border rank of the $`3\times3`$ matrix product

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because exact border rank remains unknown even for this fixed matrix-product tensor; community importance reflects degenerating bilinear algorithms and the geometry behind fast multiplication.  
**Topic:** approximate bilinear algorithms  
**Last checked:** 2026-11-27

**Status:** Partially resolved

## Problem statement

In $`\mathbb C^9\otimes\mathbb C^9\otimes\mathbb C^9`$, let

```math
M_3=\sum_{i,j,k=1}^{3}e_{ij}\otimes e_{jk}\otimes e_{ki}.
```

The tensor rank $`R(T)`$ is the minimum number of pure tensors in an exact sum
for $`T`$. The border rank $`\underline R(T)`$ is the least $`r`$ such that $`T`$ is a
Euclidean limit of tensors of rank at most $`r`$. Determine
$`\underline R(M_3)`$. The use of limits makes this a different invariant from
[AC-02](../AC-02/README.md).

## Why it matters

Degenerating bilinear algorithms underlie asymptotic
improvements in matrix multiplication.

## References and status

A. Conner, A. Harper, J. M. Landsberg,
[*New lower bounds for matrix multiplication and det₃*](https://arxiv.org/abs/1911.07981),
Theorem 1.1, proves $`\underline R(M_3)\ge17`$. Schönhage's 21-term
degeneration gives $`\underline R(M_3)\le21`$ as detailed below. J. Alman and B. Li,
[*Asymptotic Rank Speedup Theorems, Revisited*](https://arxiv.org/abs/2605.21738)
(2026), §1, identifies the exact border rank as open. The remaining values
are 17, 18, 19, 20 and 21.

## Status check — 2026-09-10

Rechecked [Alman–Li, §1](https://arxiv.org/html/2605.21738v1), and searched for a 2026 exact border-rank determination of the 3×3 multiplication tensor. The May 2026 source explicitly lists this value as open. Neither its asymptotic-rank improvements nor an exact-rank algorithm determines the border rank. No full resolution was located; the previously cited lower bound remains a bound, not an exact answer.

## Reviewed research submission — 14 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Verified affiliation and submission record](../../references/holden-ac-2026-09-14/README.md).

The audit supports the elementary pair-section/cactus and grouped Fourier arguments in Sections 2–4. Missing verifier modules and certificates prevent a full-package audit. Stronger computer-assisted claims are excluded; no exact border rank or improved endpoint is established.

[Report](../../references/holden-ac-2026-09-14/AC-03-submission.pdf) · [Independent AI-agent audit and limitations](../../references/holden-ac-2026-09-14/verification/review-ac03-ac04.md). AI assistance disclosed; no external human review, formal verification or Lean checks for this submission.

## Verified bounds — 2026-11-27

Schönhage's Example 2.3 gives a 21-term degeneration for the full
$`3\times3`$ product. This is a classical upper bound for the displayed
complex border rank. [Schönhage, *Partial and Total Matrix Multiplication*](https://doi.org/10.1137/0210032) · [Landsberg's survey, §8.1](https://people.tamu.edu/~jml/msurvey0407.pdf).

Write $`x_i=a_{i1},\ y_i=a_{i2},\ z_i=a_{i3}`$ and
$`u_i=b_{1i},\ v_i=b_{2i},\ w_i=b_{3i}`$. For the third matrix $`C=(c_{ij})`$,
the sum of products can be grouped as

```math
\begin{aligned}
F(t)={}&\sum_i(x_i+t^2y_i)(v_i+t^2u_i)c_{ii}
 -\sum_i x_i(v_i+w_i)\sum_j c_{ij}\\
 &+\sum_{i\ne j}(x_i+t^2y_j)(v_i-tu_j)c_{ij}\\
 &+\sum_{i\ne j}(x_i+t^2z_j)(w_i+tu_j)(c_{ij}+tc_{ji})\\
 &+\sum_i (x_i+t^2z_i)w_i\left(c_{ii}-t\sum_{j\ne i}c_{ji}\right),
\end{aligned}
```

where all indices run from 1 to 3. The five sums consist of
$`3+3+6+6+3=21`$ products of linear forms, one form from each of $`A,B,C`$.
Exact coefficient expansion verifies that the constant and linear terms
vanish and the quadratic coefficient is
$`\sum_{i,j}(x_ju_i+y_jv_i+z_jw_i)c_{ij}=\mathop{\mathrm{tr}}\nolimits(ABC)`$.
For each $`t\ne0`$, the tensor of $`t^{-2}F(t)`$ has rank at most 21. Its limit
at zero is the tensor of $`\mathop{\mathrm{tr}}\nolimits(ABC)`$, which is $`M_3`$ in the
displayed bases. The index pattern in the fourth sum uses $`b_{11}`$ at
$`(i,j)=(3,1)`$, correcting $`b_{12}`$ in that factor in the thesis transcription.
[Stothers, *On the Complexity of Matrix Multiplication*, pp. 22–23](https://www.maths.ed.ac.uk/sites/default/files/atoms/files/stothers.pdf).

The resulting interval is $`17\le\underline R(M_3)\le21`$. Andreini et al.'s
November revision reports numerical searches in this range. An exact
degeneration or a lower-bound certificate would be needed to improve one of
the endpoints. [Andreini et al., arXiv:2602.21797v2, §6](https://arxiv.org/html/2602.21797v2#S6).
