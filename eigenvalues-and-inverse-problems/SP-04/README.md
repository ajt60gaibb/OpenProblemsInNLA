# SP-04 — The smallest-multiplier rule for nearest unit-absolute-determinant matrices

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solution claimed  
**Last checked:** 2026-09-11  

**Rating rationale:** Challenging reflects a global root-selection rule across all dimensions and singular-value data; specialist impact is the exact projection onto a specific determinant constraint.

## Resolution claim — 2026-09-11

**Negative resolution claimed; submitted by Matthew Colbrook.** See the [complete manuscript](solution.md), **Theorem SP-04, sections 1–4** ([PDF](solution.pdf) · [LaTeX](solution.tex)), prepared 11 September 2026.

The manuscript claims that the stationary pair with uniquely smallest absolute multiplier fails to minimize the Frobenius distance for an open set of real $3\times3$ data matrices with distinct singular values in $(7/4,44/25)$. Both determinant signs are allowed. The open-set argument addresses the algebraic-generic qualifier in the original target.

The manuscript discloses generation in a ChatGPT conversation. Its full proof has not been independently verified here, and no publication or priority claim is made. [Supporting diagnostics](../../references/colbrook-2026-09-11/README.md) were rerun successfully; these are not an independent proof audit. This update checks the submitted claim against the displayed target; the dated literature checks below remain the record of the earlier search. The ratings above are historical, and this entry is excluded from the open count.

## Original problem statement

For $n\ge2$, define
$$
\mathcal G_n=\{X\in\mathbb R^{n\times n}:\det X\in\{-1,1\}\},
\qquad
\|Y\|_F^2=\sum_{i,j}y_{ij}^2.
$$
For a real data matrix $U$, consider the real stationary pairs
$$
\mathcal C(U)=
\{(X,c)\in\mathcal G_n\times\mathbb R:X^T(U-X)=cI_n\}.
$$
For generic $U$, this set is finite. Choose a pair $(X_*,c_*)$ whose multiplier has minimum absolute value. Does
$$
\|U-X_*\|_F=\min_{X\in\mathcal G_n}\|U-X\|_F
$$
hold for every $n\ge2$ and generic real $U$?

Here generic means outside an exceptional proper real algebraic set; in particular $U$ is invertible and its squared singular values are distinct. If minimum absolute multipliers tie, the question can be restricted to the generic locus where the choice is unique. The source phrases the same selection question using the real roots of its elimination polynomial $R_1(c)$, which correspond one-to-one to stationary matrices for generic data.

## Relevance
 This is a concrete question about selecting the global nearest matrix from the stationary solutions of a structured matrix nearness problem. A positive answer would supply a scalar criterion for identifying the global solution. Both determinant signs are allowed; this must not be silently replaced by projection onto $\operatorname{SL}_n(\mathbb R)$ alone.

## References

- J. A. Baaijens and J. Draisma, *Euclidean distance degrees of real algebraic groups*, Linear Algebra and its Applications 467 (2015), 174–187, §4.1, equations (4)–(5), elimination algorithm, and Problem 4.3 on p.186 ([version of record](https://pure.tue.nl/ws/files/3846347/391917266748824.pdf); [journal](https://doi.org/10.1016/j.laa.2014.11.012)).
- P. Jaap and O. Sander, *How to project onto SL(n)*, arXiv:2501.19310 (2025), introduction pp.1–2, discussing the Baaijens–Draisma conjectural global selection rule ([primary manuscript](https://arxiv.org/pdf/2501.19310)); Journal of Optimization Theory and Applications 209 (2026), article 40 ([journal](https://doi.org/10.1007/s10957-026-02974-8)).

## Status check — 2026-09-08
 The January 2025 manuscript explicitly describes the earlier proposed global-minimum selection as conjectural. Its journal version appeared in April 2026; the accessible journal abstract and arXiv version history were checked, but the subscription-only journal body was not inspected. Searches for “nearest determinant-one matrix”, “Baaijens”, “smallest absolute value”, “projection SL(n)”, and 2025–2026 found no resolution of this exact rule. The problem retains the source's generic-data scope.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

## Audit update — 2026-09-10

Rechecked [Baaijens–Draisma](https://pure.tue.nl/ws/files/3846347/391917266748824.pdf), §4.1, Problem 4.3, and [Sander's 2025 manuscript](https://arxiv.org/pdf/2501.19310), introduction. The latter still describes the global selection step as conjectural. Searches for smallest-multiplier projection results found no general proof. The positive-determinant projection problem and algorithms reaching stationary points must be distinguished from the stated $\det=\pm1$ global rule; impact is narrowed to specialist.
