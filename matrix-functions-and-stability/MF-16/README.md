# MF-16 — Uniqueness of positive definite solutions of two-letter word equations in order two

**Topic:** Structured nonlinear matrix equations.  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Last checked:** 2026-09-08

## Problem statement

A word $W(X,B)$ is a finite product of letters from $\{X,B\}$. It is symmetric if its sequence of letters equals its reversal. Require at least one occurrence of $X$.

For every such symmetric word $W$ and every pair of Hermitian positive definite matrices $B,P\in\mathbb C^{2\times2}$, is there exactly one Hermitian positive definite matrix $X\in\mathbb C^{2\times2}$ satisfying

$$
W(X,B)=P?
$$

Products are evaluated in the written order. Existence is known; uniqueness is the open assertion. This is the ordinary two-letter word case of the surviving order-two conjecture, with no real powers or additional fixed letters included in the statement.

## Why it matters

The question concerns whether a structured nonlinear matrix equation has a single positive definite solution branch. The elementary word $XBX$ connects this family with matrix geometric means and Riccati equations.

## References

- C. J. Hillar and C. R. Johnson, [Symmetric word equations in two positive definite letters](https://qualiaphile.com/files/S0002-9939-03-07163-6.pdf), *Proceedings of the American Mathematical Society* 132 (2004), 945–953, Definition 1.1, Theorem 2.2, and Conjecture 2.3. This gives the original two-letter existence and uniqueness formulation.
- S. N. Armstrong and C. J. Hillar, [Solvability of Symmetric Word Equations in Positive Definite Letters](https://arxiv.org/abs/math/0507306), *Journal of the London Mathematical Society* 76 (2007), 777–796, Theorem 1.4 and Conjecture 11.5 (p. 20 of the arXiv PDF); Remark 11.6 discusses the real order-two case.
- J. D. Lawson and Y. Lim, [Solving symmetric matrix word equations via symmetric space machinery](https://repository.lsu.edu/mathematics_pubs/611/), *Linear Algebra and its Applications* 414 (2006), 560–569. Its bounded-degree uniqueness result is summarized in Armstrong–Hillar's introduction.

## Status check

On 2026-09-08, searched the titles, “symmetric word equations”, “Conjecture 11.5”, “2 × 2”, “two-by-two”, “uniqueness”, “counterexample”, and 2025–2026. No order-two resolution was located. Armstrong–Hillar refute unrestricted uniqueness in dimensions at least three, while explicitly retaining the order-two conjecture; their special order-two theorem and known bounded-degree results do not cover every word. No recent explicit reaffirmation was found. The statement deliberately records the source-backed two-letter problem rather than presuming that the paper's comments about reducing complex matrices to real matrices cover arbitrarily many fixed letters.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
