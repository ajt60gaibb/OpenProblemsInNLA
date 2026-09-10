# TR-06 — Finite mean angular condition number for identifiable tensor decomposition

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because generic uniqueness does not supply the integrability estimates needed near degenerate decompositions; specialist importance reflects the particular angular condition number and volume-based input model.  
**Status:** Open  
**Last checked:** 2026-09-10  

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
\mathbb E_\mu\kappa_{\rm ang}(A)<\infty
$$

for every admissible format and $r\ge3$. The rank-two case is a theorem. Normalizing each recovered summand inside the derivative is part of the definition; simply dividing the regular condition number by a scalar does not give this problem.

## Reference

Beltrán, Breiding, and Vannieuwenhoven, [*The Average Condition Number of Most Tensor Rank Decomposition Problems Is Infinite*](https://doi.org/10.1007/s10208-022-09551-1), *Foundations of Computational Mathematics* 23 (2023), 433–491: equation (6), Theorem 3, and Conjecture 2. The [author preprint](https://arxiv.org/pdf/1903.05527) labels the conjecture 1.10.

## Status check — 2026-09-10

Rechecked the [journal version, equation (6), Theorem 3 and Conjecture 2](https://doi.org/10.1007/s10208-022-09551-1), and searched for higher-rank angular-condition-number proofs. The theorem covers rank two, which the displayed target already excludes; no result proving finite mean for all admissible ranks at least three was located. The 2023 conjecture is the latest explicit statement checked, and a later unlocated result cannot be ruled out.

