# TR-21 — A Seginer theorem for arbitrary independent identically distributed tensor entries

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Obtaining a uniform bound without moment control needs substantial new random-tensor analysis. Sharp injective-norm estimates matter to the community working on tensor approximation and random multilinear algorithms.

## Problem statement

Fix an integer $r\geq 3$. For integers $n_1,\ldots,n_r\geq2$, let $T\in\mathbb R^{n_1\times\cdots\times n_r}$ have independent identically distributed integrable real entries of mean zero. Its injective norm is
$$
\|T\|_{\mathrm{inj}}=
\sup_{\|x_j\|_2=1,\ 1\leq j\leq r}
|\langle T,x_1\otimes\cdots\otimes x_r\rangle|.
$$
Define the largest expected Euclidean fiber norm by
$$
F(T)=\max_{1\leq k\leq r}\mathbb E
\max_{\substack{i_j\in\{1,\ldots,n_j\}\\j\ne k}}
\left(\sum_{a=1}^{n_k}
T_{i_1,\ldots,i_{k-1},a,i_{k+1},\ldots,i_r}^{\,2}\right)^{1/2}.
$$
Do constants $0<c_r\leq C_r<\infty$, depending only on the order $r$, exist such that
$$
c_rF(T)\leq\mathbb E\|T\|_{\mathrm{inj}}\leq C_rF(T)
$$
for every such format and entry distribution?

This is Lucca–Pesenti's Conjecture 1.8, with its comparison notation written as explicit quantifiers. The entry distribution may depend on the dimensions. No variance normalization, finite higher moment, density, or dimension-independent moment-equivalence hypothesis is imposed. Integrability makes both expectations finite in every finite format. The matrix case $r=2$ is Seginer's theorem and is included only as background.

## Why it matters

The injective norm measures the largest interaction with a rank-one tensor. A fiber-based characterization would give sharp noise scales for random tensor approximation, including sparse distributions for which flattening and logarithmic losses can obscure the relevant scale.

## References and status check

1. K. Lucca and L. Pesenti, *Norm Bounds for Sparse Random Tensors and Spectral Gap of Random Hypergraphs*, [arXiv:2607.07308v1](https://arxiv.org/html/2607.07308v1), §1.3, Conjecture 1.8; Assumption 1.6, Theorem 1.7, and Appendix B describe the proved moment-restricted case.
2. Y. Seginer, *The expected norm of random matrices*, Combinatorics, Probability and Computing **9** (2000), 149–166; the matrix predecessor, identified in reference 26 of Lucca–Pesenti.

### Status check — 2026-09-10

Checked Lucca–Pesenti v1, Conjecture 1.8, Theorem 1.7 and Proposition B.1, and targeted Seginer/tensor/2026 resolution searches. Their moment-restricted theorem proves the comparison for subclasses with fixed numerical moment-equivalence parameters; its constants otherwise depend on those parameters as well as the order. These are substantive proved subclasses, so the status is Partially resolved. The requested uniformity over arbitrary integrable distributions remains open, explicitly including centered Bernoulli entries with parameter $1/n$. No full resolution was located. The matrix theorem and estimates with logarithmic losses do not settle the displayed target.
