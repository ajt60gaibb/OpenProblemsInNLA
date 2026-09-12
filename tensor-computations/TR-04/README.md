# TR-04 — Improve the worst-case approximation factor for prescribed tensor-train ranks

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because the guarantee must improve a general worst-case approximation barrier without increasing ranks; community importance reflects the central role of TT compression in numerical tensor methods.  
**Status:** Solved  
**Last checked:** 2026-09-11  

<!-- colbrook-recovered-tensors -->
## Resolution — 2026-09-11

**Affirmative resolution by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. A deterministic algorithm tests at most $`n_1`$ first-cut singular-subspace choices and TT-SVD completions. It returns a tensor within the prescribed ranks with squared error strictly less than $`(d-1)E_*`$ whenever $`E_*>0`$, and exactly reconstructs when $`E_*=0`$, in the canonical idealized arithmetic/SVD model. This settles the displayed pointwise target. It does not give a smaller uniform factor $`c<d-1`$ or a finite-precision bit-complexity guarantee; the fixed-format limiting example in Section 5 makes this distinction explicit.

[Complete manuscript, Theorem 3 and Sections 2–4](../../references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-04.pdf) · [Standalone TeX](../../references/colbrook-recovered-tensors-2026-09-11/manuscripts/TR-04.tex) · [Independent complete-source PASS review](../../references/colbrook-recovered-tensors-2026-09-11/verification/reviews/TR-04-review.md) · [Authorship and provenance](../../references/colbrook-recovered-tensors-2026-09-11/README.md).

The recovered AI-assisted proof passed independent agent review; this is not external human peer review or formal certification. The original target and dated source audit are retained. Difficulty, importance and rating rationale are historical. No novelty or priority claim is made.
<!-- /colbrook-recovered-tensors -->

## Problem statement

Let $`d\ge3`$, $`n_1,\ldots,n_d\ge2`$, and positive integers $`r_1,\ldots,r_{d-1}`$ be given. Let $`S_r\subset\mathbb R^{n_1\times\cdots\times n_d}`$ consist of tensors whose unfolding separating modes $`1,\ldots,j`$ from modes $`j+1,\ldots,d`$ has rank at most $`r_j`$, for every $`j`$. For a dense input tensor $`A`$, put

```math
E_*(A,r)=\min_{Y\in S_r}\|A-Y\|_F^2.
```

Find a polynomial-time algorithm returning $`X\in S_r`$ with

```math
\|A-X\|_F^2<(d-1)E_*(A,r)
\qquad\text{whenever }E_*(A,r)>0,
```

and exact reconstruction when $`E_*(A,r)=0`$; alternatively, establish a complexity obstruction to such a guarantee. Ranks may not be increased. Polynomial time is measured in the dense input size and rank parameters, in the idealized arithmetic/SVD model used for TT-SVD; a bit-complexity formulation must additionally specify precision and output tolerances.

This is the tensor-train case of the published tree-network question. The positive-error qualification corrects the impossible strict inequality at zero optimum. It asks for a uniformly valid algorithm, not an empirical improvement or a guarantee restricted to particular input tensors.

## References

I. V. Oseledets, [*Tensor-Train Decomposition*](https://doi.org/10.1137/090752286), *SIAM Journal on Scientific Computing* 33 (2011), 2295–2317, Theorem 2.2 and Corollary 2.4. Amsel et al., [workshop report](https://arxiv.org/html/2602.05394v3), §6.1, Problem 6.1. Matthew Fahrbach and Mehrdad Ghadiri, [*A Tight Lower Bound for the Approximation Guarantee of Higher-Order Singular Value Decomposition*](https://arxiv.org/html/2508.06693v1), Theorems 1.2–1.3, concerns tightness of specific Tucker algorithms rather than a lower bound against all tensor-train algorithms.

## Status check — 2026-09-10

Rechecked [workshop v3, §6.1, Problem 6.1](https://arxiv.org/html/2602.05394v3), which still requests a strict improvement or a complexity obstruction. Searches for tensor-train approximation improvements in 2026 also located [Yu et al., randomized block Krylov TT approximation](https://doi.org/10.3389/fams.2026.1824146): its probabilistic error estimates and practical speedups do not give the displayed universal improvement at unchanged ranks. No full resolution was located; the positive-optimum qualification remains essential.

