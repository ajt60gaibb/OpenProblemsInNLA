# MI-02 — Bourin's crossed-Heinz inequality

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** A longstanding sharp bound for all unitarily invariant norms remains beyond the known interpolation range; it would strengthen matrix-power and matrix-mean estimates.

## Problem statement

For every integer $`n\ge1`$, positive definite $`A,B\in\mathbb C^{n\times n}`$, real $`t\in[0,1]`$, and unitarily invariant norm $`|||\cdot|||`$, is

```math
|||A^tB^{1-t}+B^tA^{1-t}|||\le|||A+B|||?
```

Powers use the spectral functional calculus. A norm is unitarily invariant when $`|||UXV|||=|||X|||`$ for all unitary $`U,V`$. The positive definite formulation avoids ambiguity at exponent zero; for $`0<t<1`$ it includes the positive semidefinite case by continuity.

## Why it matters

This asks for a sharp bound on noncommuting products of fractional matrix powers. Bounds of this kind support analysis of positive definite matrix computations and the comparison of matrix means.

## References

1. J.-C. Bourin, *Matrix subadditivity inequalities and block-matrices*, International Journal of Mathematics 20(6) (2009), 679–691; the crossed-Heinz question. [Preprint](https://arxiv.org/abs/0805.1954), [DOI](https://doi.org/10.1142/S0129167X09005509).
2. F. Kittaneh and É. Ricard, *On a question of Bourin*, Linear Algebra and its Applications 710 (2025), 356–362; central parameter interval. [DOI](https://doi.org/10.1016/j.laa.2025.02.004).
3. T. Zhang, *Bourin-type inequalities for $`\tau`$-measurable operators in fully symmetric spaces*.  
   arXiv:2602.00358v1 (30 January 2026), §1, equation (1.3), Theorem 1.3. [Primary text](https://arxiv.org/html/2602.00358).

## Status check — 2026-09-10

The bound with constant one is proved for $`t\in[1/4,3/4]`$; the endpoints $`0,1`$ are immediate for positive definite matrices. The displayed assertion remains unresolved in the two outer open intervals. The latest 2026 source gives a larger explicit constant there. Searches included `Bourin crossed Heinz conjecture 2026`, `On a question of Bourin Kittaneh Ricard`, and `Bourin inequality proof counterexample 2025 2026`. No resolution of the remaining norm inequality was found. The stronger assertion for individual singular values has counterexamples and is not the present problem.

**Audit update (2026-09-10):** Rechecked Zhang’s Theorem 1.3 and searched for a later crossed-Heinz proof or counterexample. Constant one is established on $`[1/4,3/4]`$; the larger constant on the outer intervals leaves the stated question there unresolved. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
