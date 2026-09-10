# AC-03 — Border rank of the $3\times3$ matrix product

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because exact border rank remains unknown even for this fixed matrix-product tensor; community importance reflects degenerating bilinear algorithms and the geometry behind fast multiplication.  
**Topic:** approximate bilinear algorithms  
**Last checked:** 2026-09-10  
**Status:** Open  

## Problem statement

In $\mathbb C^9\otimes\mathbb C^9\otimes\mathbb C^9$, let

$$M_3=\sum_{i,j,k=1}^{3}e_{ij}\otimes e_{jk}\otimes e_{ki}.$$

The tensor rank $R(T)$ is the minimum number of pure tensors in an exact sum
for $T$. The border rank $\underline R(T)$ is the least $r$ such that $T$ is a
Euclidean limit of tensors of rank at most $r$. Determine
$\underline R(M_3)$. The use of limits makes this a different invariant from
[AC-02](../AC-02/README.md).

## Why it matters

Degenerating bilinear algorithms underlie asymptotic
improvements in matrix multiplication.

## References and status

A. Conner, A. Harper, J. M. Landsberg,
[*New lower bounds for matrix multiplication and det₃*](https://arxiv.org/abs/1911.07981),
Theorem 1.1, proves $\underline R(M_3)\ge17$. J. Alman and B. Li,
[*Asymptotic Rank Speedup Theorems, Revisited*](https://arxiv.org/abs/2605.21738)
(2026), §1, explicitly identifies this exact border rank as open. Searches for
“3x3 border rank matrix multiplication 2026” found no exact determination.
**Admitted: no resolution located.**

## Status check — 2026-09-10

Rechecked [Alman–Li, §1](https://arxiv.org/html/2605.21738v1), and searched for a 2026 exact border-rank determination of the 3×3 multiplication tensor. The May 2026 source explicitly lists this value as open. Neither its asymptotic-rank improvements nor an exact-rank algorithm determines the border rank. No full resolution was located; the previously cited lower bound remains a bound, not an exact answer.
