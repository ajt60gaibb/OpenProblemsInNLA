# MI-20 — Sharp subquadratic Lee constants for sums of matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-10

**Rating rationale:** Determining a sharp two-parameter function after the proposed formula failed is challenging; matrix-sum bounds affect norm estimates used across NLA.

## Problem statement

For a complex square matrix $`X`$, write $`|X|=(X^*X)^{1/2}`$ and $`\|X\|_p=(\mathop{\mathrm{tr}}\nolimits|X|^p)^{1/p}`$. For every integer $`m\ge2`$ and real $`1< p<2`$, determine exactly the dimension-independent constant

```math
C_p(m)=\sup_{n\ge1}\ \sup_{A_1,\ldots,A_m\in\mathbb C^{n\times n},\,\sum_j|A_j|\ne0}
\frac{\|\sum_{j=1}^m A_j\|_p}{\|\sum_{j=1}^m|A_j|\|_p}.
```

Thus the requested answer is the optimal constant, as a function of both $`p`$ and $`m`$, in the corresponding Schatten norm inequality. An upper bound alone does not settle the problem. All matrix orders are included in the same supremum.

These constants quantify the loss when replacing a matrix sum by the sum of its positive semidefinite moduli, an operation common in norm estimates for matrix computations. This is distinct from constants comparing the arithmetic and symmetric moduli of one matrix (catalog MI-09).

## References

1. X. Li, *Sharp Concave-Function Transfer for Lee-Type Schatten Norm Inequalities*, arXiv:2608.25989v1 (2026), §1, equations defining the linear constants, and §4, Problem 4.2. [Full text](https://arxiv.org/html/2608.25989).
2. Q. Tang and S. Zhang, *Generalizing Lee's conjecture on the sum of absolute values of matrices*, Linear Algebra Appl. 731 (2026), 196–204, original candidate and endpoint results. [Preprint](https://arxiv.org/abs/2510.16846).
3. H. Qiu, *Sharp quasi-reverse Minkowski inequality for Schatten norms* (2026), the two-matrix sharp result for $`p\ge2`$ and counterexamples in the subquadratic interval. [Preprint](https://arxiv.org/abs/2608.17565).

Status check (2026-09-10): Li's current v1, dated August 26, explicitly retains this problem after proving equality of the sharp linear and concave-function constants. Its §4 records failure of the Tang–Zhang candidate throughout $`1< p<2`$. Searches for the exact title, “Lee sharp Schatten constants”, and “Tang Zhang conjecture” with 2025/2026 found no later determination of this entire function. This is a bounded literature check, not a guarantee against an unindexed solution.
