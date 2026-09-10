# TR-29 — Exact partially symmetric rank of products of generalized W tensors

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Matching constructive upper bounds by sharp lower bounds for arbitrary products requires substantial new decomposition arguments. The exact partially symmetric rank of this particular family chiefly interests specialists in tensor rank and multipartite entanglement.

## Problem statement

For an integer $d\geq3$, put
$$
W_d=\sum_{j=1}^{d}
e_1^{\otimes(j-1)}\otimes e_2\otimes
e_1^{\otimes(d-j)}\in\operatorname{Sym}^d(\mathbb C^2).
$$
Given any $k\geq2$ and $d_1,\ldots,d_k\geq3$, set
$T_{\mathbf d}=W_{d_1}\otimes\cdots\otimes W_{d_k}$.
Determine the exact smallest integer $s$ such that
$$
T_{\mathbf d}=\sum_{\ell=1}^{s}
(v_{1,\ell})^{\otimes d_1}\otimes\cdots\otimes
(v_{k,\ell})^{\otimes d_k},
\qquad v_{j,\ell}\in\mathbb C^2.
$$
This minimum is the partially symmetric rank with the $k$ blocks of orders $d_1,\ldots,d_k$ fixed. It is not the border rank and not the rank obtained after grouping modes from different blocks. The harmless nonzero scalar relating the displayed $W_d$ to the polynomial $x^{d-1}y$ can be absorbed into a decomposition.

## Why it matters

These explicit tensors are benchmarks for the difference between exact, border, and symmetry-constrained tensor decompositions. They already demonstrate that decomposing two copies together can cost fewer terms than multiplying their individual ranks. Determining their exact ranks would quantify that saving beyond small examples.

## References and status check

1. A. Oneto and E. Ventura, *Ranks of tensors: geometry and applications*, [2025 survey](https://doi.org/10.1007/s40574-025-00472-9), Question 12, following Theorems 4.4–4.5.
2. E. Ballico, A. Bernardi, M. Christandl, and F. Gesmundo, *On the partially symmetric rank of tensor products of W-states and other symmetric tensors*, [arXiv:1803.01623](https://arxiv.org/abs/1803.01623), §§3–4; Rendiconti Lincei **30** (2019), 93–124.
3. S. Canino, A. Casarotti, and P. Santarsiero, *A new bound on the rank of tensor product of W-states*, [arXiv:2512.05828v1](https://arxiv.org/html/2512.05828v1), Theorem 1.1 and its following discussion.

### Status check — 2026-09-10

Checked the 2025 source question and Canino–Casarotti–Santarsiero v1, Theorem 1.1 and the ensuing sharpness discussion, with targeted W-product-rank searches through 2026. The December 2025 paper gives the upper bound $2^{k-1}(d_1+\cdots+d_k-2k+2)$ and explicit decompositions. Equality is known for $k=2,d_1=d_2=3$, where the rank is eight, so a nontrivial parameter case is resolved. The construction alone does not prove minimality for other tuples. No general exact formula was located.
