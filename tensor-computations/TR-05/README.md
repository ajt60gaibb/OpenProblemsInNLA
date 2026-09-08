# TR-05 — Infinite mean condition number in every identifiable tensor format

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open conjecture; explicit journal source published in 2023.  
**Last checked:** 2026-09-08  

## Context and notation

Fix $d\ge3$, $n_j\ge2$, and $r\ge2$. Assume generic complex identifiability: outside a proper algebraic exceptional set, a complex tensor of rank $r$ in this format has a unique unordered collection of $r$ rank-one summands. Let $M_r$ be the smooth identifiable locus of real rank-$r$ tensors, with induced Euclidean volume $dV$. The random input has density

$$
d\mu(A)=Z^{-1}e^{-\|A\|_F^2/2}\,dV(A).
$$

For the addition map $\Phi(a_1,\ldots,a_r)=\sum_i a_i$ on rank-one tensors, let $\Psi$ be a local inverse at $A$. Use Frobenius norms and their product norm. Define

$$
\kappa(A)=\|D\Psi(A)\|_2,\qquad
\kappa_{\rm ang}(A)=\|D(p^{\times r}\circ\Psi)(A)\|_2,
\quad p(a)=a/\|a\|_F.
$$

Values on measure-zero exceptional sets do not affect the expectations. This samples tensors by volume, not independent Gaussian summands.

## Problem statement

Under this probability model, prove or disprove

$$
\mathbb E_\mu\kappa(A)=\infty
$$

for every admissible format and $r\ge2$. Rank two is already proved. The unresolved task removes the additional smaller-format identifiability assumption used for the higher-rank theorem; it must not be counted again for parameter ranges covered by that theorem.

## Reference

Carlos Beltrán, Paul Breiding, and Nick Vannieuwenhoven, [*The Average Condition Number of Most Tensor Rank Decomposition Problems Is Infinite*](https://doi.org/10.1007/s10208-022-09551-1), *Foundations of Computational Mathematics* 23 (2023), 433–491: Definition 1, Assumption 1, equation (5), Theorems 1–2, and Conjecture 1. The [author preprint](https://arxiv.org/pdf/1903.05527) labels the conjecture 1.8.

## Status check

Searches included `"average condition number" "tensor" conjecture 2025 2026` and `"regular condition number" "tensor" "2026" conjecture proof`. No removal of the remaining hypothesis was located. The latest explicit conjecture located is the 2023 journal version.
