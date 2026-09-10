# MF-14 — Degree coverage with seven matrix multiplications

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because numerical evidence for coefficient-space coverage needs exact algebraic justification; community impact comes from multiplication budgets for practical matrix-function evaluation.  
**Last checked:** 2026-09-10  
**Status:** Open  

## Problem statement

Start with the scalar polynomials $1,x\in\mathbb C[x]$. Allow arbitrarily many complex linear combinations of already computed polynomials and at most seven multiplications of two already computed polynomials. Let $\mathcal P_7\subseteq\mathbb C[x]_{\le128}$ be the set of possible outputs.

Identify a polynomial with its coefficient vector in $\mathbb C^{129}$ and let $\overline{\mathcal P_7}^{\,Z}$ be its Zariski closure: the common zero set of all polynomial equations in the coefficients that vanish throughout $\mathcal P_7$. Is

$$\max\{d\in\{0,\ldots,128\}:\mathbb C[x]_{\le d}\subseteq\overline{\mathcal P_7}^{\,Z}\}=42?$$

The target concerns closure and the complex coefficient field. Exact representability of every polynomial is a stronger assertion.

## Why it matters

For a dense input matrix, matrix products dominate the cost of polynomial evaluation. The conjecture determines how much polynomial degree a budget of seven products can cover, providing a theoretical benchmark for matrix-function evaluation schemes.

## References

1. E. Jarlebring and G. Lorentzon, *The polynomial set associated with a fixed number of matrix-matrix multiplications*, arXiv:2504.01500v3 (13 August 2025), §2.2 (closure convention), §5.4, Conjecture 13. [Primary text](https://arxiv.org/html/2504.01500).
2. J. Sastre, J. Ibáñez, J. M. Alonso, and E. Defez, *Beyond Paterson–Stockmeyer: Advancing matrix polynomial computation*, WSEAS Transactions on Mathematics 24 (2025), 684–693, §4 (a five-product construction). [Primary paper](https://wseas.com/journals/mathematics/2025/b385106-036%282025%29.pdf), [DOI](https://doi.org/10.37394/23206.2025.24.68).
3. J. M. Alonso, J. Sastre, J. Ibáñez, and E. Defez, *A systematic framework for stable and cost-efficient matrix polynomial evaluation*, arXiv:2603.23143v1 (24 March 2026), abstract and conclusions. [Primary text](https://arxiv.org/html/2603.23143).

## Status check — 2026-09-08

The latest arXiv source remains v3 and labels the displayed equality a conjecture supported by computations. The later papers give constructions and stability procedures without establishing the seven-product degree-coverage claim. Searches included the exact title with `2026`, `Jarlebring Lorentzon conjecture seven multiplications 42`, and `Sastre polynomial evaluation 2026`. No resolution was located. A [3 September 2026 author talk](https://indico3.mpi-magdeburg.mpg.de/event/58/contributions/1074/) also describes higher-cost degree coverage as conjectural. Six-product real/complex formulations have a separate source ambiguity and are deliberately not included here.

## Audit — 2026-09-10

Rechecked [Conjecture 13 and Remark 14](https://arxiv.org/html/2504.01500): complex closure coverage at seven products is still conjectural, with concrete matrix-exponential applications. Title and seven-product searches found no exact proof. The [June 2026 degree-eight construction](https://arxiv.org/html/2606.24701v1) solves a different budget/degree problem.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
