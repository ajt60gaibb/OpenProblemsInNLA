# IE-01 — Forsythe's conjecture beyond restart length two

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Solution claimed  
**Last checked:** 2026-09-10  

> **SOLUTION CLAIMED — excluded from the open count.** The September 2026 paper reports a complete classification. The theorem scope was checked; this catalog has not independently verified the full proof.

**Rating rationale:** Historical ratings describe the original long-standing convergence problem and its importance for iterative linear solvers. They are not an estimate of remaining work after the claimed resolution.

## Original problem statement

Let $A\in\mathbb R^{n\times n}$ be symmetric positive definite, $b,x_0\in\mathbb R^n$, and $3\leq s<n$. At each restart, perform exactly $s$ exact-arithmetic conjugate-gradient steps, starting from the last iterate, and discard the previous search directions. Denote the iterate after restart cycle $j$ by $x_j$. Suppose this process never terminates exactly, and put

$$
r_j=b-Ax_j,\qquad y_j=r_j/\|r_j\|_2.
$$

Prove or disprove that both $(y_{2j})_{j\geq0}$ and $(y_{2j+1})_{j\geq0}$ converge in $\mathbb R^n$, for every such input and restart length. The question concerns directions, not whether the residual norms tend to zero. Exact termination is excluded so every normalization exists.

## References

Faber, Liesen, and Tichý, [*On the Forsythe conjecture*](https://doi.org/10.1007/s10543-023-00991-x), BIT 63 (2023), §2, especially the displayed Forsythe conjecture. Colbrook, Stepaniants, and Townsend, [*A Proof of the Forsythe Conjecture for the Two-Step Restarted Conjugate Gradient Method*](https://arxiv.org/abs/2608.02852), August 2026, §1 and main theorem.

## Resolution and status check — 2026-09-10

M. J. Colbrook, G. Stepaniants, and A. Townsend, *A Complete Resolution of Forsythe's Conjecture for Restarted Conjugate Gradients*, [arXiv:2609.04659v2](https://arxiv.org/abs/2609.04659v2), submitted September 4 and revised September 7, 2026, **Theorem 1.1**.

The theorem reports convergence of the even and odd normalized residual subsequences for restart lengths two and three, and counterexamples for every restart length at least four. This covers the entire original range $s\ge3$ and answers the universal conjecture negatively. The exact-arithmetic, real symmetric positive-definite and nontermination conditions match the original entry.

The current abstract, version history and theorem statement were checked. This is a full-resolution preprint claim, not a newly performed proof audit. The problem was removed from the open count on 2026-09-08; its original page is now restored so the stable ID and resolution remain visible. No part of this entry contributes to the open count.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Solved and claimed solutions](../../RESOLVED.md#ie-01) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
