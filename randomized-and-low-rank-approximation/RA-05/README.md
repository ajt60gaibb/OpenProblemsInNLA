# RA-05 — Sharp joint rank and accuracy dependence for strong $`\ell_p`$ subspace coresets

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because simultaneous control of all subspaces must match joint rank and accuracy lower bounds; community impact is compact robust low-rank fitting.  
**Last checked:** 2026-09-10  

**Status:** Open  

Fix a real $`p>2`$. For $`A\in\mathbb R^{n\times d}`$, with rows $`a_i^T`$, and a linear subspace $`F\subseteq\mathbb R^d`$, define

```math
\mathop{\mathrm{cost}}\nolimits_A(F)=\sum_{i=1}^n\|a_i^T(I-P_F)\|_2^p,
```

where $`P_F`$ is the Euclidean orthogonal projector. A strong row coreset consists of nonnegative weights $`w_1,\ldots,w_n`$, supported on a small subset of the original rows, for which

```math
(1-\varepsilon)\mathop{\mathrm{cost}}\nolimits_A(F)
\leq\sum_iw_i\|a_i^T(I-P_F)\|_2^p
\leq(1+\varepsilon)\mathop{\mathrm{cost}}\nolimits_A(F)
```

holds simultaneously for every $`F`$ of dimension at most $`k`$.

Determine the optimal worst-case coreset size as a joint function of $`k`$ and $`\varepsilon`$, up to logarithmic factors. In particular, do constants $`C_p,c_p>0`$ exist such that, for all $`n,d`$, integers $`1\leq k<d`$, all input matrices $`A`$, and all $`0<\varepsilon<1/2`$, such a coreset exists with

```math
|\mathop{\mathrm{supp}}\nolimits(w)|\leq
C_p\left(\frac{k^{p/2}}{\varepsilon}+\frac{k}{\varepsilon^2}\right)
\log^{c_p}\!\left(\frac{2k}{\varepsilon}\right)?
```

The constants may depend on fixed $`p`$, but not on $`n,d,k,\varepsilon`$. This is an existence/size question; no extra running-time target is imposed.

Such a coreset permits subsequent robust low-rank fitting on a much smaller weighted matrix. The August 2026 paper proves an upper bound of order $`\widetilde O_p(k^{p/2}/\varepsilon^2)`$ and explicitly identifies the remaining gap to the joint lower-bound expression in Section 1.4. Its new result supersedes older questions that merely asked for an $`\varepsilon^{-2}`$ dependence.

## References

1. H. Lin, V. Mirrokni, and D. P. Woodruff, *Nearly Optimal Strong Coresets for $`\ell_p`$ Subspace Approximation*, arXiv:2608.26047v2, Section 1.4 “Open problems”; Section 1.2 for the new bounds. [Paper](https://arxiv.org/html/2608.26047v2).
2. D. P. Woodruff and T. Yasuda, *Root ridge leverage score sampling for $`\ell_p`$ subspace approximation*, FOCS 2025, full version arXiv:2407.03262. [Paper](https://arxiv.org/abs/2407.03262).

## Status check — 2026-09-08

Searched “strong coresets subspace approximation p greater than 2 epsilon 2026” and the exact 2026 title; checked the latest arXiv v2 of August 27, 2026. No later resolution was found. The target comes from the remaining question in that paper, rather than its already improved predecessor bounds.

## Audit — 2026-09-10

Rechecked [Lin–Mirrokni–Woodruff, §1.4](https://arxiv.org/html/2608.26047v2) and the August 27 version record. The joint $`k,\varepsilon`$ gap remains explicit. Strong-coreset follow-up searches found no resolution. Difficulty was raised because the target concerns all input matrices and requires a new uniform sampling analysis.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
