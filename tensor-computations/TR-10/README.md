# TR-10 — Border Comon's conjecture over the complex numbers

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Rating rationale:** Extreme because equality of two secant-rank notions for all symmetric tensors remains a foundational tensor-geometry barrier; community importance concerns whether symmetry can be imposed without an approximation-rank penalty.  
**Last checked:** 2026-09-10  
**Status:** Partially resolved  

## Statement

For every integer order $`d\ge3`$, dimension $`n\ge2`$, and symmetric tensor $`T\in\mathop{\mathrm{Sym}}\nolimits^d(\mathbb C^n)`$, is

```math
\underline R(T)=\underline R_{\mathrm{sym}}(T)?
```

Here $`R(T)`$ is the least number of summands in a decomposition $`T=\sum_{j=1}^r v_{j,1}\otimes\cdots\otimes v_{j,d}`$, with complex vectors. Symmetric rank restricts each summand to $`c_jv_j^{\otimes d}`$. The border rank $`\underline R(T)`$ is the least $`r`$ for which a sequence of tensors of rank at most $`r`$ converges to $`T`$ in the entrywise Euclidean topology. Symmetric border rank instead uses symmetric tensors of symmetric rank at most $`r`$.

## Relevance

This asks whether exploiting symmetry can increase the number of rank-one terms required for arbitrarily accurate approximation. It concerns the attainable accuracy of symmetric low-rank tensor models.

## References

1. T. Mańdziuk and E. Ventura, *Symmetrization maps and minimal border rank Comon's conjecture*, arXiv:2411.05721v2, 2026. [Full text](https://arxiv.org/html/2411.05721v2), §1, opening discussion and Conjecture 1.1; the general conjecture precedes the minimal-border-rank specialization. [Version record](https://arxiv.org/abs/2411.05721).
2. J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge University Press, 2017. [Author text](https://people.tamu.edu/~jml/simonsclass.pdf), Conjecture 5.6.1.5, a three-factor formulation.

## Status check — 2026-09-10

Rechecked [Mańdziuk–Ventura v2, §1 and the main theorems](https://arxiv.org/html/2411.05721v2), and searched for 2025–2026 proofs or counterexamples. The September 2026 revision explicitly leaves the general border conjecture open while proving minimal-border-rank subfamilies. Those are genuine portions of this universal target; Shitov’s counterexample to ordinary exact-rank Comon is a different statement. No full border-rank resolution was located.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
