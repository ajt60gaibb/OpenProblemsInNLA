# NM-04 — The Rowland–Wu polynomial identity for Sinkhorn limits

**Topic:** Exact matrix scaling and balancing.  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because the full coefficient formula requires a general algebraic-combinatorial identity; community importance concerns exact formulas for a widely used matrix-scaling limit.  
**Last checked:** 2026-09-11  
**Status:** Solved  

<!-- colbrook-factorization -->
## Resolution — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the exact target.**

The complete Rowland--Wu coefficient identity holds for every positive real rectangular matrix and all $`m,n\ge1`$. The proof identifies the coefficient sum with one determinant and constructs a null vector after scaling. Vanishing minors and the cases $`m=1`$ or $`n=1`$ are included. This proves the displayed coefficients, beyond the previously known algebraic-degree bound.

The complete target is resolved. Its former difficulty rating is historical; the original statement, references and dated audits remain below.

**Primary reference:** [complete authored PDF](../../references/colbrook-factorization-2026-09-11/manuscripts/NM-04_sinkhorn_identity.pdf), [standalone TeX](../../references/colbrook-factorization-2026-09-11/manuscripts/NM-04_sinkhorn_identity.tex), **Theorem 1**. [Independent proof review](../../references/colbrook-factorization-2026-09-11/verification/reviews/NM-04-review.md) · [Authorship and submission record](../../references/colbrook-factorization-2026-09-11/README.md). Verification is independent agent review, not external human peer review or formal certification.

<!-- /colbrook-factorization -->

## Problem statement

Let $`m,n\ge1`$ and $`A\in\mathbb R_{>0}^{m\times n}`$. Let $`\mathop{\mathrm{Sink}}\nolimits(A)`$ be its Sinkhorn limit with row sums $`1`$ and column sums $`m/n`$: equivalently, the unique matrix $`D_1AD_2`$ with these sums, where $`D_1,D_2`$ are positive diagonal matrices. Set $`x=\mathop{\mathrm{Sink}}\nolimits(A)_{11}`$.

Define

```math
\mathcal D=\{(R,C):R\subseteq\{2,\ldots,m\},\ C\subseteq\{2,\ldots,n\},\ |R|=|C|\}.
```

Submatrix indices are in increasing order; empty determinants and products equal $`1`$. Put

```math
\Delta(R,C)=\det A_{\{1\}\cup R,\{1\}\cup C},\qquad
\Gamma(R,C)=a_{11}\det A_{R,C},
```

```math
M(\mathcal S)=\prod_{(R,C)\in\mathcal S}\Delta(R,C)
\prod_{(R,C)\in\mathcal D\setminus\mathcal S}\Gamma(R,C).
```

For a finite set $`U`$ of integers and $`s\in U`$, let $`p_s(U)`$ be the position of $`s`$ in the increasing list of $`U`$, starting at $`1`$. For each $`\mathcal S=\{(R_i,C_i):1\le i\le k\}\subseteq\mathcal D`$, define $`H_{\mathcal S}\in\mathbb Z^{k\times k}`$ by

```math
(H_{\mathcal S})_{ii}=|R_i|(m+n)-mn,
\qquad
\tau_{ij}=(R_i\setminus R_j,R_j\setminus R_i,C_i\setminus C_j,C_j\setminus C_i),
```

and, for $`i\ne j`$,

```math
(H_{\mathcal S})_{ij}=\begin{cases}
(-1)^{p_s(R_j)+p_t(C_j)}m,&\tau_{ij}=(\varnothing,\{s\},\varnothing,\{t\}),\\
(-1)^{p_s(R_i)+p_t(C_i)+1}n,&\tau_{ij}=(\{s\},\varnothing,\{t\},\varnothing),\\
(-1)^{p_s(C_i)+p_t(C_j)}m,&\tau_{ij}=(\varnothing,\varnothing,\{s\},\{t\}),\\
(-1)^{p_s(R_i)+p_t(R_j)}n,&\tau_{ij}=(\{s\},\{t\},\varnothing,\varnothing),\\
0,&\text{otherwise}.
\end{cases}
```

The determinant is independent of the ordering chosen for $`\mathcal S`$. Is the following identity valid for every such $`A,m,n`$?

```math
\sum_{\mathcal S\subseteq\mathcal D}
\det(m^{-1}H_{\mathcal S})M(\mathcal S)x^{|\mathcal S|}=0.
```

## Why it matters

This would give an explicit algebraic relation for entries of a ubiquitous iterative matrix scaling limit, including a structured formula for every coefficient.

## References

- E. Rowland and J. Wu, [The entries of the Sinkhorn limit of an $`m\times n`$ matrix](https://arxiv.org/abs/2409.02789), arXiv v2 (2025-05-25), notation on pp. 3–4 and Conjecture 2. The matrix denoted $`H_{\mathcal S}`$ here is their $`\mathop{\mathrm{adj}}\nolimits_{\mathcal S}(m,n)`$.
- E. Rowland, [Combinatorial structure behind Sinkhorn limits](https://ericrowland.github.io/talks/Combinatorial_structure_behind_Sinkhorn_limits_SIAM.pdf), SIAM talk, 2025-07-07, slide 13: the coefficient formula remains conjectural after the degree bound was proved.
- M. C. Fang, [Closed Form of a Generalized Sinkhorn Limit](https://arxiv.org/abs/2506.06338), 2025, abstract and the general algebraic degree bound. This settles the degree-bound consequence, rather than the displayed coefficient formula.

## Status check — 2026-09-10

Rechecked [Rowland–Wu v2, §2 and Conjecture 2](https://arxiv.org/pdf/2409.02789), including the rectangular scaling and four coefficient signs, and [Fang’s degree-bound result](https://arxiv.org/abs/2506.06338). The 3×3 coefficient formula is proved, while the determinant formula in arbitrary dimensions remains conjectural. Searches for subsequent Rowland–Wu identity proofs found no full resolution. Fang’s general degree bound alone does not establish the displayed coefficients.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
