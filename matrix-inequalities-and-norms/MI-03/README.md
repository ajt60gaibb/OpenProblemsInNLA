# MI-03 — Sharp additive triangle constant for an odd number of contractions

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale:** Sharpness for every odd summand count needs a new extremal construction or obstruction; the payoff is concentrated in operator triangle inequalities.

## Resolution — 2026-09-11

**Affirmative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

The sharp additive contraction constant is $c_k=k/4$ for every $k\ge2$, including every odd summand count. Exact dimension-two extremizers match the universal upper bound.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-03-review.md) checks the full original argument and records its hash. The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

For each integer $k\ge2$, let $c_k$ be the infimum of all $c\ge0$ such that

$$\left|\sum_{j=1}^k A_j\right|\preceq cI_n+\sum_{j=1}^k|A_j|$$

for every $n\ge1$ and all $A_1,\ldots,A_k\in\mathbb C^{n\times n}$ satisfying $\|A_j\|_2\le1$. Here $|A|=(A^*A)^{1/2}$, $\|\cdot\|_2$ denotes the operator norm, and $X\preceq Y$ means $Y-X$ is positive semidefinite.

Is $c_k=k/4$ for every odd integer $k\ge3$?

## Why it matters

The scalar absolute-value triangle inequality fails in matrix order. The optimal additive correction quantifies that failure for uniformly bounded summands, in a form usable in positive block-matrix estimates.

## References

1. J.-C. Bourin and E.-Y. Lee, *Diagonal and off-diagonal blocks of positive definite partitioned matrices*, arXiv:2307.02034v3 (15 December 2023), Corollary 4.4 and the conjecture immediately following Remark 4.5. [Primary text](https://arxiv.org/html/2307.02034).
2. E.-Y. Lee, *How to compare the absolute values of operator sums and the sums of absolute values?*, Operators and Matrices 6(3) (2012), 613–619; §2 supplies related triangle inequalities. [Primary paper](https://files.ele-math.com/articles/oam-06-42.pdf), [DOI](https://doi.org/10.7153/oam-06-42).

## Status check — 2026-09-10

Corollary 4.4 establishes $c_k\le k/4$ for every $k$ and sharpness for even $k$; the source separately conjectures sharpness for all odd $k>1$. Its latest version remains v3. Searches included `Bourin Lee contractions odd k constant k/4`, `three contractions 3/4 sharp conjecture`, and `Bourin contractions sharp 2025 2026`. The 2026 symmetric-modulus papers concern different inequalities. No resolution of this additive odd-summand problem was located.

**Audit update (2026-09-10):** Rechecked the conjecture after Remark 4.5 in Bourin–Lee and searched for odd-summand sharpness results. The proved even-summand statement is outside the target, which already restricts to odd $k$. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
