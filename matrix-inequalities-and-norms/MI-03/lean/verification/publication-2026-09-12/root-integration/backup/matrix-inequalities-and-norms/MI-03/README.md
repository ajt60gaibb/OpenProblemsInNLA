# MI-03 — Sharp additive triangle constant for an odd number of contractions

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Lean verified
**Last checked:** 2026-09-12

**Rating rationale:** Sharpness for every odd summand count needs a new extremal construction or obstruction; the payoff is concentrated in operator triangle inequalities.

## Resolution — 2026-09-11

**Affirmative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

The sharp additive contraction constant is $`c_k=k/4`$ for every $`k\ge2`$, including every odd summand count. Exact dimension-two extremizers match the universal upper bound.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-03-review.md) checks the full original argument and records its hash. The draft was AI-assisted. That original review was informal; the later Lean verification is documented below. External human peer review is not claimed. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Lean proof and verification evidence - 2026-09-12

**The complete original odd-summand conjecture is Lean verified.** The [proof at revision 901ba5f](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/901ba5ffad3b57557b60c7360df67659d8b8aa21/matrix-inequalities-and-norms/MI-03/lean) proves that $`k/4`$ is the least member of the full admissible-constant set for every $`k\ge2`$, then identifies its actual real infimum. This includes every odd $`k\ge3`$, with all positive dimensions and every tuple of complex contractions. Genuine principal CFC moduli and Euclidean operator norms are used; no literature inequality is assumed as an unproved premise.

**Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook** retains authorship of the mathematical proof and result; **Jean-Christophe Bourin and Eun-Young Lee** retain the original conjecture and prior-bound credit.

The eight [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/901ba5ffad3b57557b60c7360df67659d8b8aa21/matrix-inequalities-and-norms/MI-03/lean/Solution.lean), each with prefix `NLA.MI03.`, are:

- `modulus_semantics`: genuine positive square root, square and norm identities.
- `contraction_modulus`: positive modulus defects for every complex contraction.
- `positive_decomposition`: the exact universal Gram-sum and positive-square identity.
- `universal_upper_bound`: admissibility of $`k/4`$ for every $`k\ge2`$.
- `root_of_unity_data`: exact complex roots and their vanishing geometric sums.
- `sharpness_witness`: true moduli, unit operator norms and full sums of the two-dimensional extremizers.
- `sharp_constant`: actual least admissible constant and infimum, for every $`k\ge2`$.
- `odd_contraction_conjecture`: the complete original assertion.

Two independent agents approved the [statements and completed proof](lean/reviews/). [Linux run 34722618003](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34722618003) matched all eight declarations with the sandboxed Comparator and replayed the solution in Lean's default kernel. The [original artifacts and operational audit](lean/verification/linux-2026-09-12/) bind all 173 input files and both actual isolation/rejection-control suites. All 16 [internal/public transitive axiom reports](lean/verification/linux-2026-09-12/axiom-verification.json) use exactly `propext`, `Classical.choice` and `Quot.sound`. The operational reviewer also served as final proof referee 1; these roles do not count as a third mathematical referee. External human peer review is not claimed.

The pins are **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). LeanCert audits this exact proof's kernel trust; there is **no numerical interval certificate**. Symbolic identities and all-$`k`$ roots avoid numerical phase approximation or interval subdivision. The source's extra three-dimensional Hermitian extremizers and rank classification are outside these exports; the complete original target is covered. See the [project guide](lean/README.md), [manifest](lean/formalization.yaml) and [dependency pins](lean/lake-manifest.json). From the immutable verified revision on a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-03/lean \
  /absolute/path/to/nla-lean-tools
```

## Problem statement

For each integer $`k\ge2`$, let $`c_k`$ be the infimum of all $`c\ge0`$ such that

```math
\left|\sum_{j=1}^k A_j\right|\preceq cI_n+\sum_{j=1}^k|A_j|
```

for every $`n\ge1`$ and all $`A_1,\ldots,A_k\in\mathbb C^{n\times n}`$ satisfying $`\|A_j\|_2\le1`$. Here $`|A|=(A^*A)^{1/2}`$, $`\|\cdot\|_2`$ denotes the operator norm, and $`X\preceq Y`$ means $`Y-X`$ is positive semidefinite.

Is $`c_k=k/4`$ for every odd integer $`k\ge3`$?

## Why it matters

The scalar absolute-value triangle inequality fails in matrix order. The optimal additive correction quantifies that failure for uniformly bounded summands, in a form usable in positive block-matrix estimates.

## References

1. J.-C. Bourin and E.-Y. Lee, *Diagonal and off-diagonal blocks of positive definite partitioned matrices*, arXiv:2307.02034v3 (15 December 2023), Corollary 4.4 and the conjecture immediately following Remark 4.5. [Primary text](https://arxiv.org/html/2307.02034).
2. E.-Y. Lee, *How to compare the absolute values of operator sums and the sums of absolute values?*, Operators and Matrices 6(3) (2012), 613–619; §2 supplies related triangle inequalities. [Primary paper](https://files.ele-math.com/articles/oam-06-42.pdf), [DOI](https://doi.org/10.7153/oam-06-42).

## Status check — 2026-09-10

Corollary 4.4 establishes $`c_k\le k/4`$ for every $`k`$ and sharpness for even $`k`$; the source separately conjectures sharpness for all odd $`k>1`$. Its latest version remains v3. Searches included `Bourin Lee contractions odd k constant k/4`, `three contractions 3/4 sharp conjecture`, and `Bourin contractions sharp 2025 2026`. The 2026 symmetric-modulus papers concern different inequalities. No resolution of this additive odd-summand problem was located.

**Audit update (2026-09-10):** Rechecked the conjecture after Remark 4.5 in Bourin–Lee and searched for odd-summand sharpness results. The proved even-summand statement is outside the target, which already restricts to odd $`k`$. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
