# AC-11 — The least positive permanent of a sign matrix

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because divisibility alone gives no construction attaining the bound for every order; specialist importance concerns exact permanent values and discrete matrix constructions.  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

## Problem statement

For $n\ge1$, let $\Omega_n=\{-1,1\}^{n\times n}$ and define
$$
\operatorname{per}A=\sum_{\sigma\in S_n}\prod_{i=1}^n a_{i,\sigma(i)},
\qquad
p_n=\min\{\operatorname{per}A:A\in\Omega_n,\ \operatorname{per}A>0\}.
$$
The set in this minimum is nonempty, since the all-ones matrix has permanent $n!$.
Is Kräuter's proposed formula
$$
p_n=2^{\,n-\lfloor\log_2(n+1)\rfloor}
$$
valid for every $n$? The problem asks for attainability of the divisibility lower bound, with no rank restriction on $A$.

## Relevance and ratings

This is an extremal question about a basic multilinear matrix function on discrete matrices. Exact values and divisibility constraints matter for permanent computation and constructions of sign matrices. The attainability problem across all orders merits challenging difficulty; its main audience is combinatorial matrix theory.

## References

- I. M. Wanless, [*Permanents of matrices of signed ones*](https://users.monash.edu.au/~iwanless/papers/wangconjLAMA.pdf), Linear and Multilinear Algebra **53** (2005), 427–433, §3, for attaining constructions through order twenty.
- D. Ingram and A. Razborov, *On the range of the permanent of $(\pm1)$-matrices*, Linear Algebra Appl. 743 (2026), 271–285. The precise question is §6, Problem 3 in [arXiv:2507.09433v1](https://arxiv.org/html/2507.09433v1); the [published introduction](https://doi.org/10.1016/j.laa.2026.04.027) gives the displayed unified formula.
- M. V. Budrevich and A. E. Guterman, *Kräuter conjecture on permanents is true*, J. Combin. Theory A 162 (2019), 306–343 ([paper](https://arxiv.org/abs/1810.04439); [journal](https://doi.org/10.1016/j.jcta.2018.11.009)), for a different, resolved rank-dependent upper-bound conjecture.

## Status check — 2026-09-10

Checked [Ingram–Razborov’s August 2026 published introduction](https://doi.org/10.1016/j.laa.2026.04.027), which explicitly retains the minimum-positive-value conjecture, and its [preprint §6, Problem 3](https://arxiv.org/html/2507.09433v1). [Wanless (2005), §3, pp. 430–431](https://users.monash.edu.au/~iwanless/papers/wangconjLAMA.pdf), supplies attaining matrices for every $n\le20$, a proved parameter range of this target. Exact-title and minimum-positive-permanent searches found no general resolution. The [2019 Kräuter theorem](https://arxiv.org/abs/1810.04439) proves a rank-dependent upper bound; [Hunter–Kwan–Sauermann](https://arxiv.org/abs/2509.22577) proves exponential range cardinality. Neither establishes general attainment of the lower bound.
