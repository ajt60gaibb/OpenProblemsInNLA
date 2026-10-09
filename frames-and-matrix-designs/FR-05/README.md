# FR-05 — Vanishing injectivity probability at 4d minus 5 complex phase measurements

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved
**Last checked:** 2026-10-08

**Rating rationale:** The asymptotic typical-injectivity question needs quantitative algebraic and probabilistic control beyond positive failure probability; it informs phase-retrieval measurement design.


## Original statement

For every integer $`d\geq2`$, draw $`A_d\in\mathbb C^{(4d-5)\times d}`$ with independent standard complex Gaussian entries: the real and imaginary parts are independent $`N(0,1/2)`$. Let $`p_d`$ be the probability that

```math
|A_dx|=|A_dy|\quad\Longrightarrow\quad
y=e^{\mathrm i\theta}x\ \text{for some }\theta\in\mathbb R
```

holds for all $`x,y\in\mathbb C^d`$, where absolute value is componentwise. Equivalently, $`p_d`$ is the probability that the induced phase-retrieval map on vectors modulo global phase is injective.

Is

```math
\lim_{d\to\infty}p_d=0?
```

This is part (b) of Vinzant's conjecture as restated in Randomstrasse 101. It distinguishes injective exceptional measurement systems from typical matrices at a row count just below $`4d-4`$. Injectivity is the basic identifiability requirement before conditioning and stable numerical inversion can be addressed.

## Resolution — independently audited 8 October 2026

Zhangsong Li's [13-page manuscript](https://zhangsong-li.github.io/injectivity_phase_retrieval.pdf), Theorem 1.4, proves the stronger bound

```math
p_d\leq C/d\qquad(d\geq2)
```

for an absolute constant $`C>0`$. This implies the displayed limit. The argument plants a two-dimensional ambiguity, compares its law in $`L^2`$ to a covariance-matched Gaussian law, and uses a quantitative implicit-function argument to turn the planted approximate ambiguity into an exact one.

An [independent AI-agent proof audit](../../reviews/2026-10-08-claimed-solutions/FR-05.md) checked the manuscript's planted and reference laws, the cone and overlap estimates, the small-ball and Newton arguments, and the final probability reduction. No proof gap was found. This supports **Solved** under the catalog's informal-audit rule; it is not external human peer review or `Lean verified`. The original target, permanent identifier, and canonical path are unchanged.

### Local Lean development — 27 September 2026

The [Lean solution](lean/Solution.lean) now proves the bound $`p_d\le C/d`$ for every $`d\ge2`$ and the original limit $`p_d\to0`$, using the original Gaussian law and all-signals injectivity predicate. The recorded local build and transitive axiom audit pass, using only standard Lean axioms and no proof placeholders in the solution. See the [final assembly](lean/FINAL_ASSEMBLY.md), [source guide](lean/README.md), and [local verification record](lean/verification/library-cleanup/README.md). An independent statement review and isolated Linux Comparator/kernel verification remain outstanding for `Lean verified`; the 8 October promotion rests on the manuscript proof audit above.

## References

1. A. S. Bandeira et al., *Randomstrasse 101: Open Problems of 2025*, arXiv:2603.29571 (2026), Conjecture 19(b). [Paper](https://arxiv.org/html/2603.29571v1).
2. C. Vinzant, *A small frame and a certificate of its injectivity*, SAMPTA 2015, arXiv:1502.04656. The explicit 11-vector frame in $`\mathbb C^4`$ demonstrates why the below-$`4d-4`$ regime cannot simply be dismissed. [Paper](https://arxiv.org/abs/1502.04656).
3. Z. Li, *Resolution of Vinzant's Conjecture on Phase Retrieval Injectivity* (13 September 2026), Theorem 1.4. The manuscript proves $`p_d\le C/d`$ for every $`d\ge2`$; the audited copy is pinned by SHA-256 in the [review](../../reviews/2026-10-08-claimed-solutions/FR-05.md). [Manuscript](https://zhangsong-li.github.io/injectivity_phase_retrieval.pdf).
4. Z. Li, *On Injectivity of Phase Retrieval*, arXiv:2606.17922 (2026). This earlier version established only $`p_d<1`$. [Paper](https://arxiv.org/abs/2606.17922).

## Historical status check — 2026-09-10

Searched “Vinzant conjecture injectivity probability limit”, “phase retrieval 4M-5 2026”, and checked the latest June 2026 paper abstract/version. Its positive probability of noninjectivity does not supply an asymptotic lower bound tending to one. The already proved assertion $`p_d<1`$ is deliberately excluded from this problem.

**Audit update (2026-09-10):** Rechecked Li’s June 2026 abstract and searched for the asymptotic part of Vinzant’s conjecture. The reported strict inequality $`p_d<1`$ does not force $`p_d\to0`$; this entry contained only the latter target. This was a bounded literature check, not a proof that no solution existed at that time.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Formalisation plan](formalisation-plan.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
