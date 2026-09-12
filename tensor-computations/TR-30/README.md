# TR-30 — Dimension of tensor loci with prescribed minimum border subrank

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Exact dimensions beyond the generic range require substantial control of tensor degenerations and stronger arguments than current bounds. The immediate audience is specialists in the geometry of tensor subrank.

## Problem statement

Let $`\mathbb F`$ be an algebraically closed field, let $`k\geq3`$, and fix positive integers $`n_1,\ldots,n_k`$ and $`1\leq r\leq\min_jn_j`$. For
$`T\in V=\mathbb F^{n_1}\otimes\cdots\otimes\mathbb F^{n_k}`$,
say that $`\underline Q(T)\geq r`$ when

```math
\sum_{a=1}^r e_a^{\otimes k}\in
\overline{\{(L_1\otimes\cdots\otimes L_k)T:
L_j\in\mathop{\mathrm{Hom}}\nolimits(\mathbb F^{n_j},\mathbb F^r)\}}^{\,\mathrm{Zar}}.
```

Thus $`\underline Q(T)`$ is border subrank, defined through degeneration to a diagonal unit tensor.

Determine, for every such field and tuple of integers, the dimension

```math
\dim X_r^{(n_1,\ldots,n_k)},\qquad
X_r^{(n_1,\ldots,n_k)}
=\{T\in V:\underline Q(T)\geq r\}.
```

The dimension of this constructible locus means the Krull dimension of its Zariski closure in the affine tensor space. This convention does not assert that the locus itself is closed. The requested output is its exact dimension as a function of the parameters; determining only an asymptotic order or only the generic subrank does not complete the question.

## Why it matters

Border subrank measures how many independent diagonal computations a tensor can approximate after transformations of its modes. The dimension asks how large the families with a specified computational capability are. It is a geometric complement to the better-understood low-border-rank varieties used in decomposition problems.

## References and status check

1. A. Oneto and E. Ventura, *Ranks of tensors: geometry and applications*, [2025 survey](https://doi.org/10.1007/s40574-025-00472-9), Question 14 in §4.4.
2. C.-Y. Chang, *Maximal border subrank tensors*, [arXiv:2208.04281](https://arxiv.org/abs/2208.04281); [Linear and Multilinear Algebra **73** (2025), 525–535](https://doi.org/10.1080/03081087.2024.2352456), the dimension lower-bound theorem.
3. B. Biaggi, C.-Y. Chang, J. Draisma, and F. Rupniewski, *Border subrank via a generalised Hilbert–Mumford criterion*, [arXiv:2402.10674v2](https://arxiv.org/html/2402.10674v2), §1 (arbitrary algebraically closed fields), Proposition 1 (constructibility), and Theorem 3 (dimension upper bound); Advances in Mathematics **461** (2025), 110077.

4. P. Pielasa, M. Šafránek, and A. Shatsila, *Exact values of generic subrank*, [arXiv:2408.07550](https://arxiv.org/pdf/2408.07550), Theorem 3.7 (all infinite fields).
5. J. Draisma, *(Border) subranks of tensors*, [September 2026 conference abstract](https://www.combinatorial-synergies.de/activities/2026-09_AnnualConference/), “Ordinary border subrank” bullet; an announcement of a restricted result.

### Status check — 2026-09-10

Checked the 2025 source question, Biaggi–Chang–Draisma–Rupniewski v2, and targeted dimension searches through 2026. There is a proved exact range: by Pielasa–Šafránek–Shatsila, Theorem 3.7, let $`g=\min\{n_1,\ldots,n_k,\lfloor(\sum_i n_i-k+1)^{1/(k-1)}\rfloor\}`$. Generic tensors have ordinary subrank $`g`$ over every infinite field. Since border subrank is at least ordinary subrank, $`X_r`$ contains a dense open subset and has dimension $`\prod_i n_i`$ whenever $`r\le g`$. This deduction resolves that range, not the remaining dimensions. Draisma’s abstract for the September 14–16, 2026 conference announces sharp bounds for equal-format tensors of maximal border subrank; the abstract supplies no proof or all-format formula. No complete resolution was located.
