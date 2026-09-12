# TR-18 — Near-optimal type-2 bound for Gaussian sums of symmetric tensors

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because the low-p regime encounters an explicit geometric barrier in tensor concentration; broad importance spans probability, analysis, theoretical computer science and noisy tensor computation.  
**Last checked:** 2026-09-10  
**Status:** Partially resolved  

## Statement

For a symmetric real tensor $`T\in(\mathbb R^d)^{\otimes r}`$, define

```math
\|T\|_{\mathcal I_p}=\max_{\|x\|_p\le1}|\langle T,x^{\otimes r}\rangle|.
```

For every integer $`r\ge2`$ and real $`2\le p<\infty`$, do constants $`C_{r,p}>0`$ and $`a_{r,p}\ge0`$ exist such that, for every $`d\ge2`$, $`N\ge1`$, and deterministic symmetric tensors $`T_1,\ldots,T_N\in(\mathbb R^d)^{\otimes r}`$,

```math
\mathbb E\left\|\sum_{i=1}^N g_iT_i\right\|_{\mathcal I_p}
\le C_{r,p}\,d^{1/2-1/p}[\log(2+dN)]^{a_{r,p}}
\left(\sum_{i=1}^N\|T_i\|_{\mathcal I_p}^{2}\right)^{1/2},
```

where $`g_i`$ are independent real $`N(0,1)`$ random variables? Constants and logarithmic exponents must be independent of $`d,N`$ and the tensors. The explicit logarithmic form spells out the source's $`\widetilde O_{r,p}`$ notation.

## Relevance

This would control the injective norm of tensor perturbations with general covariance, extending a central matrix concentration principle to multilinear computation and noisy tensor models.

## References

1. A. S. Bandeira, D. Dmitriev, K. Lucca, P. Nizić-Nikolac, and A. Rödder, *Randomstrasse101: Open Problems of 2025*, arXiv:2603.29571, 2026. [Primary text](https://arxiv.org/html/2603.29571v1), Entry 8 by K. Lucca, Conjecture 16 and equations (1)–(2).
2. A. S. Bandeira, S. Gopi, H. Jiang, K. Lucca, and T. Rothvoss, *A Geometric Perspective on the Injective Norm of Sums of Random Tensors*. [Primary preprint](https://arxiv.org/abs/2411.10633), introduction and tensor type-2 bounds; published as *Tensor Concentration Inequalities: A Geometric Approach*, STOC 2025.

## Status check — 2026-09-10

Rechecked [Randomstrasse101, Entry 8, Conjecture 16](https://arxiv.org/html/2603.29571v1) and the [underlying tensor-concentration paper](https://arxiv.org/abs/2411.10633), then searched for later type-2 bounds. The displayed inequality is proved for p at least twice the tensor order and for the matrix case r=p=2; the general low-p regime remains unresolved in the August 2026 manuscript. No full resolution was located. Restrictions on covariance or summands do not establish the universal claim.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
