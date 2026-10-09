# TR-21 — A Seginer theorem for arbitrary independent identically distributed tensor entries

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved  
**Last checked:** 2026-10-01

**Rating rationale:** Obtaining a uniform bound without moment control needs substantial new random-tensor analysis. Sharp injective-norm estimates matter to the community working on tensor approximation and random multilinear algorithms.

## Problem statement

Fix an integer $`r\geq 3`$. For integers $`n_1,\ldots,n_r\geq2`$, let $`T\in\mathbb R^{n_1\times\cdots\times n_r}`$ have independent identically distributed integrable real entries of mean zero. Its injective norm is

```math
\|T\|_{\mathrm{inj}}=
\sup_{\|x_j\|_2=1,\ 1\leq j\leq r}
|\langle T,x_1\otimes\cdots\otimes x_r\rangle|.
```

Define the largest expected Euclidean fiber norm by

```math
F(T)=\max_{1\leq k\leq r}\mathbb E
\max_{\substack{i_j\in\{1,\ldots,n_j\}\\j\ne k}}
\left(\sum_{a=1}^{n_k}
T_{i_1,\ldots,i_{k-1},a,i_{k+1},\ldots,i_r}^{\,2}\right)^{1/2}.
```

Do constants $`0< c_r\leq C_r<\infty`$, depending only on the order $`r`$, exist such that

```math
c_rF(T)\leq\mathbb E\|T\|_{\mathrm{inj}}\leq C_rF(T)
```

for every such format and entry distribution?

This is Lucca–Pesenti's Conjecture 1.8, with its comparison notation written as explicit quantifiers. The entry distribution may depend on the dimensions. No variance normalization, finite higher moment, density, or dimension-independent moment-equivalence hypothesis is imposed. Integrability makes both expectations finite in every finite format. The matrix case $`r=2`$ is Seginer's theorem and is included only as background.

## Resolution — 2026-10-01

**Affirmative resolution.** Theorem 1.1 of the supplied revised manuscript, *A Seginer theorem for random tensors with arbitrary iid integrable entries* (30 September 2026), proves

```math
F(T)\leq\mathbb E\|T\|_{\mathrm{inj}}\leq C_rF(T),
```

where $`C_r`$ depends only on the tensor order. See the [complete manuscript](../../references/haidary-resolutions-2026-09-30/TR-21-Seginer-comparison-revised.pdf) and its [preserved LaTeX source](../../references/haidary-resolutions-2026-09-30/TR-21-Seginer-comparison-revised.tex), Theorem 1.1 and Sections 2–6. The result covers every rectangular format in the original statement and every integrable iid mean-zero real entry law, including dimension-dependent laws, without a finite-variance or higher-moment assumption. The maximum over modes in $`F(T)`$ remains outside the expectation. Thus it answers the full Lucca–Pesenti Conjecture 1.8; Corollary 1.2 includes centered Bernoulli entries at every density.

**Attribution and contribution.** The proof builds on Zhou–Zhu's shared-class discrepancy, joint-rate and heavy-tuple arguments in [arXiv:2609.20520v1](https://arxiv.org/abs/2609.20520v1), Lemmas 4.4–4.5 and 5.1, Proposition 4.6 and Appendix A. The manuscript's additional step extends that framework across magnitude labels: shared coordinate classes are charged once across the labels, and fiber and variance contributions are summed with squared amplitudes before the reduction to arbitrary integrable laws. It imports Lucca–Pesenti's sparse-tail estimate from [Theorem 1.4 and Corollary 4.3](https://arxiv.org/html/2607.07308v1), distinct from their moment-restricted comparison, and Seginer's matrix comparison from [Corollary 2.2](https://doi.org/10.1017/S096354830000420X) for elongated rectangular formats. Lucca–Pesenti are also credited for the conjecture. The attribution section, point-of-use citations and bibliography acknowledge the [Kahn–Szemerédi light–heavy lineage](https://doi.org/10.1145/73007.73063) and [Zhou–Zhu's earlier sparse-tensor work](https://doi.org/10.1214/21-EJS1838).

**Review evidence.** The submitter reports an audit by **ChatGPT 6 Pro**; the [supplied audit and revision transcript](https://chatgpt.com/share/6abd7541-acb0-83ed-a0bc-fde3f977bf84) audits the full integrable-law comparison and records the citation and presentation corrections incorporated in this revision. This is an informal AI audit, not formal proof-assistant certification or external human peer review. **Solved** records that audit level under the catalog policy. The original target, historical ratings and dated literature check below are retained; this notice supersedes the earlier partial status.

## Why it matters

The injective norm measures the largest interaction with a rank-one tensor. A fiber-based characterization would give sharp noise scales for random tensor approximation, including sparse distributions for which flattening and logarithmic losses can obscure the relevant scale.

## References and status check

1. K. Lucca and L. Pesenti, *Norm Bounds for Sparse Random Tensors and Spectral Gap of Random Hypergraphs*, [arXiv:2607.07308v1](https://arxiv.org/html/2607.07308v1), §1.3, Conjecture 1.8; Assumption 1.6, Theorem 1.7, and Appendix B describe the proved moment-restricted case.
2. Y. Seginer, *The expected norm of random matrices*, Combinatorics, Probability and Computing **9** (2000), 149–166; the matrix predecessor, identified in reference 26 of Lucca–Pesenti.

### Status check — 2026-09-10

Checked Lucca–Pesenti v1, Conjecture 1.8, Theorem 1.7 and Proposition B.1, and targeted Seginer/tensor/2026 resolution searches. Their moment-restricted theorem proves the comparison for subclasses with fixed numerical moment-equivalence parameters; its constants otherwise depend on those parameters as well as the order. These are substantive proved subclasses, so the status is Partially resolved. The requested uniformity over arbitrary integrable distributions remains open, explicitly including centered Bernoulli entries with parameter $`1/n`$. No full resolution was located. The matrix theorem and estimates with logarithmic losses do not settle the displayed target.
