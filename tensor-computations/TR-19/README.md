# TR-19 — Exact best-rank-one approximation ratios for general tensor formats

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because exact constants across all tensor formats involve unresolved extremal tensor geometry; community importance is the sharp energy captured by rank-one approximation and its role in iterative decomposition.  
**Topic:** Tensor approximation and norm comparison.  
**Last checked:** 2026-09-10  
**Status:** Partially resolved  

For integers $d\ge3$ and $2\le n_1\le\cdots\le n_d$, let $V=\mathbb R^{n_1\times\cdots\times n_d}$. For $T\in V$, define

$$
\|T\|_F^2=\sum_{i_1=1}^{n_1}\cdots\sum_{i_d=1}^{n_d}T_{i_1\ldots i_d}^2,
$$

$$
\|T\|_\sigma=\max_{\substack{x_j\in\mathbb R^{n_j}\\\|x_j\|_2=1,\ 1\le j\le d}}
\left|\sum_{i_1=1}^{n_1}\cdots\sum_{i_d=1}^{n_d}
T_{i_1\ldots i_d}\prod_{j=1}^d(x_j)_{i_j}\right|.
$$

Determine, as a function of the dimensions, the exact value

$$
\tau(n_1,\ldots,n_d)=\min_{T\in V\setminus\{0\}}\frac{\|T\|_\sigma}{\|T\|_F}.
$$

Equivalently, determine the largest constant $\tau$ for which $\tau\|T\|_F\le\|T\|_\sigma$ holds for every tensor in that format. The target is the sharp constant for general formats, not merely another upper or lower bound. All formats constitute one problem.

This ratio measures the worst-case amount of tensor energy accessible to a best rank-one approximation and is relevant to convergence analyses of successive rank-one approximation methods.

## References

1. Z. Li and Y.-B. Zhao, [On norm compression inequalities for partitioned block tensors](https://pure.port.ac.uk/ws/portalfiles/portal/19117904/On_norm_compression_inequalities.pdf), *Calcolo* 57 (2020), article 11, §5, equation (15), pp. 15–16. The text explicitly identifies determination of the general extremal ratio as the outstanding problem.
2. Z. Li, Y. Nakatsukasa, T. Soma, and A. Uschmajew, [On orthogonal tensors and best rank-one approximation ratio](https://arxiv.org/abs/1707.02569), *SIAM Journal on Matrix Analysis and Applications* 39 (2018), 400–425, abstract and characterization of equality in the basic dimension bound.
3. K. Kozhasov and J. Tonelli-Cueto, [Probabilistic bounds on best rank-one approximation ratio](https://arxiv.org/abs/2201.02191), arXiv v2 (2022-09-23), abstract and bounds for general and partially symmetric tensors.

## Status check — 2026-09-10

Rechecked [Li–Zhao, §5](https://pure.port.ac.uk/ws/portalfiles/portal/19117904/On_norm_compression_inequalities.pdf), [Li et al. on orthogonal tensors](https://arxiv.org/abs/1707.02569), and [Kozhasov–Tonelli-Cueto](https://arxiv.org/abs/2201.02191), and searched for later exact-ratio results. Orthogonal-tensor formats give exact values for substantive subfamilies; the general-format formula remains unresolved. Probabilistic upper bounds do not determine it. No newer full resolution was located.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
