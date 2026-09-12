# IE-12 — Near-quadratic solution cost at a prescribed backward error

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** broadly interesting  
**Status:** Solved  
**Last checked:** 2026-09-12  

**Rating rationale (historical):** Challenging reflects the remaining removal of a dimension-dependent logarithm from an established general algorithm; broad impact follows from a condition-independent cost bound for arbitrary linear systems.

## Resolution: affirmative, 12 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Verified affiliation and submission record](../../references/holden-ie12-2026-09-12/README.md).

[Theorem 1, proved in Sections 2–6](solution.pdf) gives a randomized exact-real algorithm with deterministic worst-case cost $`O(n^2\varepsilon^{-3})`$ and $`O(n^2)`$ scalar storage. For every original input it always returns a nonzero vector and achieves the original A-only backward error at most $`5\varepsilon/8`$ with probability greater than $`0.997`$. Thus it settles the complete target with $`q=3`$, uniformly in dimension, conditioning and right-hand side. [Proof source](solution.tex).

The argument passed a separate [independent Codex AI-agent audit](../../references/holden-ie12-2026-09-12/independent-review.md), including exact component-test reproduction. This is informal automated review, not external human peer review or formal verification. The supplied draft was prepared with ChatGPT assistance; no Lean verification was performed.

Entrywise randomized rounding and weighted-pattern matrix products cancel the logarithmic iteration overhead in total arithmetic cost. This does not assert dimension-independent black-box convergence, finite-precision stability, bit complexity or practical speed. The original target and prior-source attribution below are retained; the earlier status discussion is historical.

## Problem statement

Does there exist a randomized algorithm and absolute constants $`C,q>0`$ such
that, for every $`n\ge1`$, nonsingular $`A\in\mathbb R^{n\times n}`$ with
$`\|A\|_2=1`$, $`b\ne0`$, and $`0<\varepsilon<1/2`$, it returns $`x\ne0`$ satisfying

```math
\Pr\left\{\frac{\|Ax-b\|_2}{\|A\|_2\|x\|_2}
\le\varepsilon\right\}\ge0.99
```

using at most $`C n^2\varepsilon^{-q}`$ operations? Use an exact-real arithmetic
model with scalar arithmetic, square roots, comparisons, and independent
standard Gaussian or random-bit draws at unit cost. All input entries may be
accessed; the norm normalization is an input promise. The cost constants must
be independent of the condition number and of $`n,b,\varepsilon`$.
The fraction is normwise backward error with perturbations allowed in $`A`$
only. A deterministic algorithm meeting the bound would also answer positively.

## References and status

M. Dereziński, Y. Nakatsukasa, and E. Rebrova,
[*Towards Universal Convergence of Backward Error in Linear System Solvers*](https://arxiv.org/html/2604.16075v2)
(22 May 2026), §§1, 3.1, 5.2, 7, poses the cost question and specifies the
backward-error metric. Corollary 17 gives $`O(n^2/\sqrt\varepsilon)`$ for PSD
systems. The revised paper's Corollary 25 proves the general-system bound
$`O(n^2\log(n/\delta)/\varepsilon)`$ with failure probability $`\delta`$;
its §7 asks for convergence independent of dimension. The remaining target
here removes the $`\log n`$ overhead, which cannot be hidden in a constant
depending only on $`\varepsilon`$. The model and success probability above
make this explicit. Searches on 2026-09-08 for “universal backward error 2026
linear systems”, “MINBERR smoothed analysis”, and “quadratic backward error
linear solver” found no resolution of the displayed bound. The earlier
version's lack of a proved general-system rate is no longer current.

## Audit update — 2026-09-10

Rechecked [version 2](https://arxiv.org/html/2604.16075v2), Corollaries 17 and 25 and §7. Positive definite inputs satisfy the displayed cost by Corollary 17; the general bound still contains $`\log n`$. This warrants partial status and a difficulty change from extreme to challenging for the narrowed remaining gap. Searches for universal backward-error convergence and MINBERR follow-ups found no dimension-independent general bound.
