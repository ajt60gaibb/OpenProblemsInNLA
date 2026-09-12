# TR-28 — Entropy formula for the asymptotic subrank of Dicke tensors

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Matching the entropy upper bound for this structured tensor family requires substantial progress beyond its known binary and multilinear cases. Tensor restriction rates and entanglement conversion give the question community importance.

## Problem statement

Let $`n\geq2`$ and let $`d_1,\ldots,d_n`$ be positive integers with $`k=d_1+\cdots+d_n`$. In $`(\mathbb C^n)^{\otimes k}`$, define the Dicke tensor

```math
D_{\mathbf d}=
\sum_{\substack{(i_1,\ldots,i_k)\in\{1,\ldots,n\}^{k}\\
|\{j:i_j=a\}|=d_a\ \text{for all }a}}
e_{i_1}\otimes\cdots\otimes e_{i_k}.
```

For any tensor $`T\in V_1\otimes\cdots\otimes V_k`$, its subrank $`Q(T)`$ is the largest integer $`s`$ for which there are linear maps $`L_j:V_j\to\mathbb C^s`$ satisfying

```math
(L_1\otimes\cdots\otimes L_k)T=\sum_{a=1}^{s}e_a^{\otimes k}.
```

Let $`\widetilde Q(T)=\lim_{m\to\infty}Q(T^{\boxtimes m})^{1/m}`$, where powers group corresponding modes.

Does every Dicke tensor satisfy

```math
\widetilde Q(D_{\mathbf d})
=2^{H(d_1/k,\ldots,d_n/k)},\qquad
H(p_1,\ldots,p_n)=-\sum_{a=1}^np_a\log_2p_a?
```

The maps in the subrank definition are arbitrary complex linear maps, independently chosen in each mode. No symmetry or coordinate-selection constraint is imposed. Multiplying $`D_{\mathbf d}`$ by a nonzero scalar does not change the question, so this agrees with the symmetric-tensor convention for the monomial $`x_1^{d_1}\cdots x_n^{d_n}`$.

## Why it matters

Subrank measures how many independent scalar computations a tensor can perform after linear transformations. The conjecture predicts the exponential rate obtainable from repeated copies of an explicit structured tensor solely from its multiplicity distribution.

## References and status check

1. P. Vrana and M. Christandl, *Asymptotic entanglement transformation between W and GHZ states*, [arXiv:1310.3244](https://arxiv.org/pdf/1310.3244), §VI, equation (40), p.10; Journal of Mathematical Physics **56** (2015), 022204. The conversion-rate formulation is reciprocal to the base-two logarithm of asymptotic subrank.
2. A. Oneto and E. Ventura, *Ranks of tensors: geometry and applications*, [2025 survey](https://doi.org/10.1007/s40574-025-00472-9), Conjecture 4.26, states the displayed subrank formula explicitly.
3. M. Christandl, P. Vrana, and J. Zuiddam, *Asymptotic tensor rank of graph tensors: beyond matrix multiplication*, [Computational Complexity **28** (2019), 57–111](https://ir.cwi.nl/pub/28609/28609.pdf), introduction and tight-tensor lower-bound results.

### Status check — 2026-09-10

Checked the source formulation and the explicit 2025 restatement, Conjecture 4.26, with targeted Dicke-tensor/subrank/entropy searches through 2026. The formula is established for $`n=2`$ and for $`d_1=\cdots=d_n=1`$, substantive parameter families within this target. The all-multiplicity statement remains conjectural in the survey, and no full later resolution was located. Asymptotic-rank computations and lower bounds on subrank do not by themselves establish the requested equality.
