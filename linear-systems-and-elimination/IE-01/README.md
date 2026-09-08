# IE-01 — Forsythe's conjecture beyond restart length two

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** open; the case of restart length two has a recent proof claim.  
**Last checked:** 2026-09-08  

## Problem statement

Let $A\in\mathbb R^{n\times n}$ be symmetric positive definite, $b,x_0\in\mathbb R^n$, and $3\leq s<n$. At each restart, perform exactly $s$ exact-arithmetic conjugate-gradient steps, starting from the last iterate, and discard the previous search directions. Denote the iterate after restart cycle $j$ by $x_j$. Suppose this process never terminates exactly, and put

$$
r_j=b-Ax_j,\qquad y_j=r_j/\|r_j\|_2.
$$

Prove or disprove that both $(y_{2j})_{j\geq0}$ and $(y_{2j+1})_{j\geq0}$ converge in $\mathbb R^n$, for every such input and restart length. The question concerns directions, not whether the residual norms tend to zero. Exact termination is excluded so every normalization exists.

## References

Faber, Liesen, and Tichý, [*On the Forsythe conjecture*](https://doi.org/10.1007/s10543-023-00991-x), BIT 63 (2023), §2, especially the displayed Forsythe conjecture. Colbrook, Stepaniants, and Townsend, [*A Proof of the Forsythe Conjecture for the Two-Step Restarted Conjugate Gradient Method*](https://arxiv.org/abs/2608.02852), August 2026, §1 and main theorem.

## Status check

Searches for `Forsythe conjecture 2026 proof` found the August preprint. Its claimed theorem covers $s=2$, not all $s\geq3$. The surviving range is therefore stated explicitly; older claims that every $s\geq2$ remains open are obsolete.
