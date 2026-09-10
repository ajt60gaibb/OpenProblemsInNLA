# TR-12 — Classification of perfect tensor formats with generic unique decomposition

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because excluding every further perfect identifiable format is a global classification problem; community importance comes from determining when generic tensor factors are uniquely recoverable at the dimension threshold.  
**Last checked:** 2026-09-10  
**Status:** Partially resolved  

## Statement

Let $d\ge3$, $n_1,\ldots,n_d\ge2$, and suppose the dimension-count value
$$
r_*={\prod_{i=1}^d n_i\over 1+\sum_{i=1}^d(n_i-1)}
$$
is an integer. Such a format is called perfect. The conjecture asserts that a generic tensor in $\bigotimes_{i=1}^d\mathbb C^{n_i}$ has a unique minimal-length decomposition as a sum of rank-one tensors if and only if, after permuting factors, the format is
$$
(2,k,k)\ (k\ge2),\qquad(3,4,5),\qquad(2,2,2,3).
$$
Generic means on a nonempty Zariski-open subset of the entire tensor space. Rank one means $v_1\otimes\cdots\otimes v_d$ with nonzero complex factors. Two decompositions are the same when their rank-one tensor summands agree after permutation; reciprocal rescalings within a summand create no new decomposition. No symmetry constraints are imposed.

## Relevance

This determines whether a decomposition algorithm can uniquely recover components of a generic tensor at the parameter-count threshold. The exceptional positive cases support explicit decomposition algorithms.

## References

1. J. D. Hauenstein, L. Oeding, G. Ottaviani, and A. J. Sommese, *Homotopy techniques for tensor decomposition and perfect identifiability*, J. reine angew. Math. 753 (2019), 1–22. [DOI](https://doi.org/10.1515/crelle-2016-0067); [primary preprint](https://arxiv.org/pdf/1501.00090), §1, equation (2) and Conjecture 1.3, p.3; Theorems 1.1–1.2 establish the two sporadic positive cases.
2. A. Massarenti, M. Mella, and G. Staglianò, *Effective identifiability criteria for tensors and polynomials*, J. Symbolic Comput. 87 (2018), 227–237. [Author PDF](https://www.iris.unict.it/retrieve/dfe4d22d-829e-bb0a-e053-d805fe0a78d9/Massarenti__Mella__Staglian%C3%B2_-_Effective_identi%EF%AC%81ability_criteria_for_tensors_and_polynomials.pdf), §1, discussion of the Hauenstein et al. generic-identifiability conjecture.

## Status check — 2026-09-10

Rechecked [Hauenstein et al., Theorems 1.1–1.2 and Conjecture 1.3](https://arxiv.org/pdf/1501.00090), and searched for later perfect-format classifications. The listed positive cases are proved, while exhaustiveness of the nonsymmetric list remains conjectural. The solved symmetric analogue does not imply this claim. No full resolution was located; the 2019 publication remains the latest explicit source checked for this exact classification.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
