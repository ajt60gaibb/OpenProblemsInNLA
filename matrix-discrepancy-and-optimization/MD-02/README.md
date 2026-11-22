# MD-02 — The sharp Lovász-theta constant for random circulant graphs

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solution claimed

**Last checked:** 2026-11-22

**Rating rationale:** Historical rating of the original target. The Fourier-constrained random optimization problem required sharper analysis than the known order bounds and matters to structured matrix optimization and sampling.


> **Affirmative solution claimed (2026-11-22).** Shanmu Jin's
> [*The sharp Lovász theta constant for two random graph models*](../../references/jin-md02-2026-11-22/manuscript.pdf),
> Theorem 1, model (2) (p. 1), and Section 3 (pp. 7–14), prove the
> expectation limit through every order, including even orders.
> [Lean proof and verification evidence](#lean-proof-and-verification-evidence)
> checks the original model, SDP and limit. Independent catalog review is pending.

For each $`n\ge2`$, partition $`\mathbb Z_n\smallsetminus\{0\}`$ into classes $`\{s,-s\}`$ (a singleton when $`s=-s`$). Select each class independently with probability $`1/2`$ and let $`S`$ be their union. Form the simple undirected graph $`G_n`$ on $`\mathbb Z_n`$ with $`\{i,j\}`$ an edge exactly when $`i-j\in S`$.

For any graph on $`n`$ vertices put

```math
\vartheta(G)=\max\Bigl\{\sum_{i,j}X_{ij}:X\in\mathbb R^{n\times n},\ X=X^T\succeq0,\ \mathop{\mathrm{tr}}\nolimits X=1,\ X_{ij}=0\text{ if }\{i,j\}\in E(G)\Bigr\}.
```

**Conjecture.** $`\displaystyle\lim_{n\to\infty}\mathbb E\vartheta(G_n)/\sqrt n=1`$.

Cyclic symmetry reduces this semidefinite program to a linear program involving the discrete Fourier matrix, connecting its typical optimum with structured sampling.

## References

1. A. S. Bandeira, D. Dmitriev, K. Lucca, P. Nizić-Nikolac, and A. Rödder, *Randomstrasse101: Open Problems of 2025*, Entry 9, Conjecture 18. [Archived paper](https://arxiv.org/abs/2603.29571).
2. A. S. Bandeira, J. Błasiok, D. Dmitriev, U. Faure, A. Kireeva, and D. Kunisky, *The Lovász number of random circulant graphs*, SampTA 2025. [Paper](https://arxiv.org/abs/2502.16227); [published DOI](https://doi.org/10.1109/SampTA64769.2025.11133544).

3. X. Chen, H. Hu, Y. Hu, W. Wang, and L. Yang, *Sharp asymptotics for the Lovász number of random circulant graphs*, arXiv:2610.22971v1, Theorem 1.1. [Primary source](https://arxiv.org/abs/2610.22971v1).
4. Shanmu Jin, *The sharp Lovász theta constant for two random graph models*, Theorem 1, model (2), and Section 3. [Manuscript PDF](../../references/jin-md02-2026-11-22/manuscript.pdf) · [LaTeX source](../../references/jin-md02-2026-11-22/manuscript.tex).

## Status check — 2026-09-10

The 2026 collection retains the conjecture and cites the 2025 partial bounds, including an upper bound of order $`\sqrt{n\log\log n}`$. Searches for subsequent sharp asymptotics and resolutions found none. Independent edge sampling on all vertex pairs is the different ensemble in MD-01.

**Audit update (2026-09-10):** Rechecked the 2026 Conjecture 18 and the SampTA paper, then searched for sharp random-circulant asymptotics. Added the published DOI; the remaining logarithmic upper-bound factor does not settle the limit. This is a bounded literature check, not a proof that no solution exists.

## Reviewed progress — 2026-09-13

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Submission and verified affiliation](../../references/holden-md02-2026-09-13/README.md).

The [manuscript](../../references/holden-md02-2026-09-13/manuscript.pdf) ([source](../../references/holden-md02-2026-09-13/manuscript.tex)), Theorems 4.1, 5.1, 6.1 and 7.1, gives an exact complementary-barrier fixed point, global Picard convergence, an equivalent converged-root expectation criterion, and uniform second-moment bounds for the first two iterates. A separate [independent Codex AI-agent informal audit](../../references/holden-md02-2026-09-13/independent-review.md) passed these supporting results.

**MD-02 remained Open after that review.** The required estimate on the converged root was unproved in Holden's submission. Bounds for two finite iterates do not control an unbounded iteration count. The submission settled no asymptotic subcase of the displayed expectation limit and therefore supported neither Solved nor Partially resolved. Its numerical checks supplement the proofs. The review asserted no Lean verification, external human peer review or priority claim.

## Scope and prior work — 2026-11-22

Chen et al., Theorem 1.1, establish the sharp expectation limit through all
odd orders, including composite orders. Jin's Section 3 treats the residue
classes over every cyclic group, with one fair bit for the singleton
antipodal class at even orders. The proof combines the complement lower
bound with a Fourier smoothing upper bound. Leaf-sum counts and tree
fields give a trial vector, and the Fourier sign-sum tail controls the
exceptional events in the expectation. The result covers the full
displayed limit.

## Lean proof and verification evidence

The [published Lean project](https://github.com/jinshanmu/LovaszTheta/tree/79d3682466a040230b751f3c8cf588fe75d7e46e/Lean)
pins Lean v4.36.0 and [mathlib v4.36.0](https://github.com/leanprover-community/mathlib4/tree/fc4f59e577feb1a4956671bc04ac18aaaf8cd842).
[CirculantLimit.lean](https://github.com/jinshanmu/LovaszTheta/blob/79d3682466a040230b751f3c8cf588fe75d7e46e/Lean/LovaszTheta/CirculantLimit.lean)
proves `LovaszTheta.Circulant.tendsto_normalizedExpectedTheta` for
all positive orders.

The [catalog statement check](../../references/jin-md02-2026-11-22/verification/MD02Check.lean)
proves that the sampled graph takes one bit per nonzero inversion class,
including a singleton for a self-inverse nonzero residue. It identifies the
formalized theta value with the attained maximum of the real symmetric,
positive semidefinite, trace-one program above. The catalog expectation
averages the optimum over the entire bit cube with equal weights.
`MD02Verification.tendsto_catalogExpectation_div_sqrt` proves the displayed
limit with orders indexed by $`n=m+2`$.

The submitter reran the build, linter and catalog statement check from a fresh
clone at the pinned revision. The six declarations in the transitive axiom
report depend only on `propext`, `Classical.choice` and `Quot.sound`.
Independent catalog review is pending.
[Reproduction commands](../../references/jin-md02-2026-11-22/README.md#reproduce-the-lean-check) ·
[Dated verification log](../../references/jin-md02-2026-11-22/verification/2026-11-22.txt)

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
