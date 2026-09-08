# TR-10 — Border Comon's conjecture over the complex numbers

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Last checked:** 2026-09-08

## Statement

For every integer order $d\ge3$, dimension $n\ge2$, and symmetric tensor $T\in\operatorname{Sym}^d(\mathbb C^n)$, is
$$
\underline R(T)=\underline R_{\mathrm{sym}}(T)?
$$
Here $R(T)$ is the least number of summands in a decomposition $T=\sum_{j=1}^r v_{j,1}\otimes\cdots\otimes v_{j,d}$, with complex vectors. Symmetric rank restricts each summand to $c_jv_j^{\otimes d}$. The border rank $\underline R(T)$ is the least $r$ for which a sequence of tensors of rank at most $r$ converges to $T$ in the entrywise Euclidean topology. Symmetric border rank instead uses symmetric tensors of symmetric rank at most $r$.

## Relevance

This asks whether exploiting symmetry can increase the number of rank-one terms required for arbitrarily accurate approximation. It concerns the attainable accuracy of symmetric low-rank tensor models.

## References

1. T. Mańdziuk and E. Ventura, *Symmetrization maps and minimal border rank Comon's conjecture*, arXiv:2411.05721v2, 2026. [Full text](https://arxiv.org/html/2411.05721v2), §1, opening discussion and Conjecture 1.1; the general conjecture precedes the minimal-border-rank specialization. [Version record](https://arxiv.org/abs/2411.05721).
2. J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge University Press, 2017. [Author text](https://people.tamu.edu/~jml/simonsclass.pdf), Conjecture 5.6.1.5, a three-factor formulation.

## Status check — 2026-09-08

The September 3, 2026 revision of reference 1 describes the general conjecture as open and proves special minimal-border-rank cases. Searches `"border rank Comon" 2026 proof` and `"Comon" "border" "counterexample" "2025" OR "2026"` located no general resolution. The ordinary exact-rank Comon conjecture was disproved by Shitov; that counterexample does not settle this border-rank question. This is a bounded literature check, not a proof of absence of a solution.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
