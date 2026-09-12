# IS-02 — Where a symmetric stochastic matrix can be spectrally unique

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11  

**Rating rationale:** Challenging reflects the geometry of isospectral stochastic families in arbitrary dimension; specialist impact concerns the narrow property of spectral uniqueness within that class.

## Resolution — 2026-09-11

**Negative resolution by Matthew J. Colbrook** (Department of Applied Mathematics and Theoretical Physics, University of Cambridge). See the [complete manuscript](solution.md), **Theorem IS-02, sections 1–2** ([PDF](solution.pdf) · [LaTeX](solution.tex)), prepared 11 September 2026.

The order-four counterexample is real symmetric, nonnegative and stochastic, has spectrum $`\{1,1,0,-1\}`$ and positive trace, and is spectrally unique up to permutation. It lies outside every segment in the proposed locus, disproving the universal necessary condition at an allowed dimension.

The original proof draft was generated in a ChatGPT conversation. A separate Codex agent independently verified the full proof and its match to the exact target on 11 September 2026: [detailed PASS review](../../references/colbrook-2026-09-11/verification/reviews/IS-02-review.md). The review records a hash of the unchanged proof text. This is independent agent verification, not external human peer review or formal certification. [The submission history and diagnostic record](../../references/colbrook-2026-09-11/README.md) preserve the initial solution claim. The ratings above are historical, and the earlier literature checks below are retained.

## Problem statement

For $`n\geq4`$, put
$`\mathcal S_n=\{A\in\mathbb R^{n\times n}:A=A^T,\ A\geq0,\ A\mathbf1=\mathbf1\}`$
and $`C_n=(\mathbf1\mathbf1^T-I)/(n-1)`$. A matrix $`A\in\mathcal S_n`$
is *spectrally unique* if every $`B\in\mathcal S_n`$ with the same eigenvalues,
including multiplicities, satisfies $`B=R^TAR`$ for a permutation matrix $`R`$.
Let $`[X,Y]=\{(1-t)X+tY:0\leq t\leq1\}`$.

Prove or disprove the following necessary condition: every spectrally unique
$`A\in\mathcal S_n`$ with $`\mathop{\mathrm{tr}}\nolimits A>0`$ belongs to

```math
[I,C_n]\ \cup\!
\bigcup_{V\in\mathop{\mathrm{vert}}\nolimits(\mathcal S_n)}
\bigl([I,V]\cup[C_n,V]\bigr).
```

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
