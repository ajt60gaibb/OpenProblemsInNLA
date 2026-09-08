# MI-06 — Thompson-type domination for the arithmetic symmetric modulus

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Last checked:** 2026-09-08

## Problem statement

For $X\in\mathbb C^{n\times n}$, define $|X|=(X^*X)^{1/2}$ and

$$S(X)=\frac{|X|+|X^*|}{2}.$$

For every $n\ge1$ and every $X,Y\in\mathbb C^{n\times n}$, do there exist unitary $U,V\in\mathbb C^{n\times n}$ such that

$$S(X+Y)\preceq\sqrt2\bigl(U S(X)U^*+V S(Y)V^*\bigr)?$$

Here $P\preceq Q$ means $Q-P$ is positive semidefinite. The conjectured universal factor $\sqrt2$ is already known to be necessary.

## Why it matters

Symmetrizing the left and right polar factors removes their directional preference. The question asks for a precise matrix-order bound for sums, which would yield singular-value and norm consequences for these positive representatives.

## References

1. T. Zhang, *Operator symmetric moduli and sharp triangle inequalities*, arXiv:2603.01046v1 (1 March 2026), §1.2, Conjecture 1.6. [Primary text](https://arxiv.org/html/2603.01046).
2. J.-C. Bourin and E.-Y. Lee, *Some hybrid matrix triangle inequalities*, arXiv:2606.29188v1 (28 June 2026), introduction, Theorems 1.1 and 1.3. [Primary text](https://arxiv.org/html/2606.29188).

## Status check — 2026-09-08

Both latest arXiv records remain v1. The June paper supplies related estimates but no proof of the displayed two-unitary inequality. Searches included `Zhang Conjecture 1.6 symmetric moduli`, `arithmetic symmetric modulus Thompson conjecture 2026`, and the two titles with `proof`. No resolution was located. The analogous theorem for the quadratic symmetric modulus is proved and must not be confused with this conjecture; a formula labeled Conjecture 3.13 in arXiv:2606.15624 appears to misidentify the modulus, so the draft follows Zhang's original statement.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
