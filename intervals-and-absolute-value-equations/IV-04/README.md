# IV-04 — Exact solution hulls for tridiagonal interval systems

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-10

**Rating rationale:** Removing the remaining complexity obstruction for genuinely tridiagonal interval systems appears to require new analysis, warranting challenging. Community impact comes from exact uncertainty bounds for a common structured linear system.

**Area:** interval linear systems; computational complexity  

## Problem statement

The input is an $n\times n$ tridiagonal interval matrix $\mathcal T$, $n\ge1$, and an interval vector $\mathcal b\subset\mathbb R^n$, all with rational endpoints. Thus $T_{ij}=0$ for $|i-j|>1$, and the remaining entries of $T$ and all entries of $b$ range independently through their supplied closed intervals. Define the united solution set

$$
\Sigma(\mathcal T,\mathcal b)=\{x\in\mathbb R^n:\exists T\in\mathcal T\ \exists b\in\mathcal b,\ Tx=b\}.
$$

Does a deterministic algorithm compute its exact coordinatewise interval hull in time polynomial in the total binary input length? It must report an empty solution set when appropriate; otherwise it must return

$$
\left[\inf_{x\in\Sigma}x_i,\ \sup_{x\in\Sigma}x_i\right],\qquad i=1,\ldots,n,
$$

with infinite endpoints explicitly represented. Finite endpoints are returned exactly as rationals. No regularity promise is imposed: intervals crossing zero and singular members are included. The input/output convention makes the source's request for a polynomial exact-hull algorithm precise; the target is the smallest box, rather than an arbitrary enclosure.

This is distinct from computing the determinant range of the same interval family. It asks for rigorous optimal error bars on the solution vector of a structured uncertain linear system.

## References

Jaroslav Horáček, Milan Hladík, and Michal Černý, [*Interval Linear Algebra and Computational Complexity*](https://arxiv.org/pdf/1602.00349), §1.4.3, “Structured systems,” pp. 16–18; published in *Applied and Computational Matrix Analysis*, Springer (2017), 37–66, [chapter DOI](https://doi.org/10.1007/978-3-319-49984-0_3).

Milan Hladík, [*An overview of polynomially computable characteristics of special interval matrices*](https://doi.org/10.1007/978-3-030-31041-7_16), Springer (2020), 295–310; [arXiv:1711.08732v1](https://arxiv.org/pdf/1711.08732), §2, p. 3, second open question.

## Status check

Both sources explicitly leave the tridiagonal hull problem open; bidiagonal systems are treated separately as polynomially solvable. Searches on 2026-09-10 for tridiagonal interval systems, exact/tight solution hulls, polynomial complexity, and 2025/2026 found no classification. The existing IV-02 screen explains why later symbolic algorithms using nonstandard interval multiplication do not settle independent-entry range questions. General interval-system hardness alone does not classify the tridiagonal restriction.

## Independent audit — 2026-09-10

The full 2017 chapter, §1.4.3, Theorem 9, proves exact hull computation for regular bidiagonal intervals, a substantive subclass of this tridiagonal target. Its proof uses division by diagonal intervals, and the end of that section explicitly assumes bounded solution sets. The treatment here of singular members and unbounded or empty solution sets is an editorial extension of that chapter’s question; the 2018 preprint’s §2 states the question without an explicit regularity promise. Even the general regular tridiagonal case remains unresolved in the checked sources and subsequent searches.
