# MF-01 — Optimal sign approximation with a multiplication budget

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because multiplication complexity and uniform approximation must be optimized together; community impact comes from sign, projector, and polar computations.  
**Status:** Partially resolved  
**Last checked:** 2026-11-28  

## Problem statement

For $`m\in\mathbb N_0`$ and $`0<\delta<1`$, put

```math
I_\delta=[-1,-\delta]\cup[\delta,1].
```

Let $`\mathcal P_m`$ consist of real polynomials computed from $`1,x`$ by
straight-line programs using at most $`m`$ nonscalar multiplications; real linear
combinations cost nothing. Define

```math
E_m(\delta)=\inf_{p\in\mathcal P_m}
\max_{x\in I_\delta}|p(x)-\mathop{\mathrm{sign}}\nolimits(x)|.
```

Determine matching asymptotic upper and lower bounds for $`E_m(\delta)`$, with
the dependence on both $`m`$ and $`\delta`$ explicit. Infima avoid assuming
attainment. The arithmetic model concerns a single polynomial identity valid for
matrices of every size.

## References and status evidence

### Exact minimax reduction for zero through three products

For every $`0<\delta<1`$ and $`m\in\{0,1,2,3\}`$, the budgeted infimum
equals the ordinary minimax error over odd polynomials of degree at most
$`2s_m-1`$, where $`(s_0,s_1,s_2,s_3)=(1,1,2,4)`$. In particular, the
[proof and explicit bounds](small-budgets.md) give
$`E_m(\delta)=\Theta((1-\delta)^{s_m})`$ uniformly in $`\delta`$ for
these four budgets. For $`m=0,1`$ the exact error is
$`(1-\delta)/(1+\delta)`$, and the proof gives the exact cubic formula
for $`m=2`$. The three-product case uses the fact that every real octic
has a three-product evaluation, so odd septics can be approximated
arbitrarily closely in coefficient space in the same budget. The proof
also gives a high-order recursive upper bound at larger budgets. Matching
bounds with an unrestricted, increasing multiplication budget remain open.

### Sources

Amsel et al.,
[Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop](https://arxiv.org/html/2602.05394v3),
§6.3, Problem 6.3 (2026). Rubensson, Jarlebring and Lorentzon,
[Recursive expansion of the matrix step function using polynomials of degree eight](https://arxiv.org/html/2606.24701v1),
§7 (June 2026), still identifies optimal recursive expansion as open. Its
particular algorithm does not establish the unrestricted optimum above.

## Audit — 2026-09-10

Rechecked the [workshop's Problem 6.3](https://arxiv.org/html/2602.05394v3#S6.SS3) and the [degree-eight follow-up, §7](https://arxiv.org/html/2606.24701v1). Neither determines the unrestricted optimum. Searches for optimal sign approximation and recursive-expansion follow-ups found no resolution; this is a bounded literature check.
