# MF-01 — Optimal sign approximation with a multiplication budget

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open; explicit 2026 problem  
**Last checked:** 2026-09-08  

## Problem statement

For $m\in\mathbb N_0$ and $0<\delta<1$, put

$$
I_\delta=[-1,-\delta]\cup[\delta,1].
$$

Let $\mathcal P_m$ consist of real polynomials computed from $1,x$ by
straight-line programs using at most $m$ nonscalar multiplications; real linear
combinations cost nothing. Define

$$
E_m(\delta)=\inf_{p\in\mathcal P_m}
\max_{x\in I_\delta}|p(x)-\operatorname{sign}(x)|.
$$

Determine matching asymptotic upper and lower bounds for $E_m(\delta)$, with
the dependence on both $m$ and $\delta$ explicit. Infima avoid assuming
attainment. The arithmetic model concerns a single polynomial identity valid for
matrices of every size.

## References and status evidence

Amsel et al.,
[Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop](https://arxiv.org/html/2602.05394v3),
§6.3, Problem 6.3 (2026). Rubensson, Jarlebring and Lorentzon,
[Recursive expansion of the matrix step function using polynomials of degree eight](https://arxiv.org/html/2606.24701v1),
§7 (June 2026), still identifies optimal recursive expansion as open. Its
particular algorithm does not establish the unrestricted optimum above.
