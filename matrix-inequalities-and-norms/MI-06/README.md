# MI-06 — Thompson-type domination for the arithmetic symmetric modulus

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale:** The arithmetic modulus lacks the useful order structure of the quadratic modulus; a solution would advance a focused family of operator triangle estimates.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

No finite constant permits the proposed two-unitary Loewner-order domination for the arithmetic symmetric modulus, already in dimension three. A fixed rational example also refutes the proposed $`\sqrt2`$ constant. This concerns matrix order, not a separate norm triangle inequality.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-06-review.md) checks the full original argument and records its hash. The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

For $`X\in\mathbb C^{n\times n}`$, define $`|X|=(X^*X)^{1/2}`$ and

```math
S(X)=\frac{|X|+|X^*|}{2}.
```

For every $`n\ge1`$ and every $`X,Y\in\mathbb C^{n\times n}`$, do there exist unitary $`U,V\in\mathbb C^{n\times n}`$ such that

```math
S(X+Y)\preceq\sqrt2\bigl(U S(X)U^*+V S(Y)V^*\bigr)?
```

Here $`P\preceq Q`$ means $`Q-P`$ is positive semidefinite. The conjectured universal factor $`\sqrt2`$ is already known to be necessary.

## Why it matters

Symmetrizing the left and right polar factors removes their directional preference. The question asks for a precise matrix-order bound for sums, which would yield singular-value and norm consequences for these positive representatives.

## References

1. T. Zhang, *Operator symmetric moduli and sharp triangle inequalities*, arXiv:2603.01046v1 (1 March 2026), §1.2, Conjecture 1.6. [Primary text](https://arxiv.org/html/2603.01046).
2. J.-C. Bourin and E.-Y. Lee, *Some hybrid matrix triangle inequalities*, arXiv:2606.29188v1 (28 June 2026), introduction, Theorems 1.1 and 1.3. [Primary text](https://arxiv.org/html/2606.29188).

## Status check — 2026-09-10

Both latest arXiv records remain v1. The June paper supplies related estimates but no proof of the displayed two-unitary inequality. Searches included `Zhang Conjecture 1.6 symmetric moduli`, `arithmetic symmetric modulus Thompson conjecture 2026`, and the two titles with `proof`. No resolution was located. The analogous theorem for the quadratic symmetric modulus is proved and must not be confused with this conjecture; a formula labeled Conjecture 3.13 in arXiv:2606.15624 appears to misidentify the modulus, so the draft follows Zhang's original statement.

**Audit update (2026-09-10):** Rechecked Zhang Conjecture 1.6 and Bourin–Lee Theorem 1.3, with searches for later symmetric-modulus resolutions. Submajorization is weaker than the required two-unitary positive-semidefinite domination. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
