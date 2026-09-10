# IS-02 — Where a symmetric stochastic matrix can be spectrally unique

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Open  
**Last checked:** 2026-09-10  

**Rating rationale:** Challenging reflects the geometry of isospectral stochastic families in arbitrary dimension; specialist impact concerns the narrow property of spectral uniqueness within that class.

## Problem statement

For $n\geq4$, put
$\mathcal S_n=\{A\in\mathbb R^{n\times n}:A=A^T,\ A\geq0,\ A\mathbf1=\mathbf1\}$
and $C_n=(\mathbf1\mathbf1^T-I)/(n-1)$. A matrix $A\in\mathcal S_n$
is *spectrally unique* if every $B\in\mathcal S_n$ with the same eigenvalues,
including multiplicities, satisfies $B=R^TAR$ for a permutation matrix $R$.
Let $[X,Y]=\{(1-t)X+tY:0\leq t\leq1\}$.

Prove or disprove the following necessary condition: every spectrally unique
$A\in\mathcal S_n$ with $\operatorname{tr}A>0$ belongs to

$$
[I,C_n]\ \cup\!
\bigcup_{V\in\operatorname{vert}(\mathcal S_n)}
\bigl([I,V]\cup[C_n,V]\bigr).
$$

Here a vertex is an extreme point of the indicated convex polytope; it need
not be a permutation matrix. Only the stated implication is asserted.
This asks where recovering a nonnegative symmetric stochastic matrix from its
spectrum can be unique up to relabeling, a different issue from mere spectral
feasibility.

## References

Mourad and Abbas, [2013 preprint](https://arxiv.org/pdf/1310.1273),
definitions in §1 and Conjecture 5.1, p. 10;
[published article](https://doi.org/10.1080/03081087.2014.903590),
*Linear and Multilinear Algebra* 63 (2015), 869–881.

## Earlier status check — 2026-09-08

Searches for the exact title, `symmetric doubly stochastic
Conjecture 5.1`, and author/title combinations with `counterexample` and
`2026` found no resolution. The source solves order three, which is excluded
from the remaining statement above.

## Audit update — 2026-09-10

Rechecked [Mourad–Abbas](https://arxiv.org/pdf/1310.1273), §5, Conjecture 5.1, against the trace and locus restrictions here. Searches for spectrally unique symmetric stochastic matrices and later work on that conjecture found no general answer. The order-three classification is outside the displayed unresolved dimensions, so it does not change this entry's status. Evidence remains historical rather than a recent explicit reaffirmation.
