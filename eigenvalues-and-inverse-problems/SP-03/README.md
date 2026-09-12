# SP-03 — The Euclidean distance degree of the real symplectic group

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Open  
**Last checked:** 2026-09-10  

**Rating rationale:** Challenging reflects an all-ranks algebraic critical-point count with only low-rank computations; specialist impact concerns the algebraic complexity of symplectic matrix nearness.

For each $`m\ge1`$, set

```math
J=\begin{pmatrix}0&I_m\\-I_m&0\end{pmatrix},\qquad
\mathop{\mathrm{Sp}}\nolimits_{2m}(\mathbb C)=
\{X\in\mathbb C^{2m\times2m}:X^TJX=J\}.
```

For a generic data matrix $`U\in\mathbb C^{2m\times2m}`$, let $`D_m`$ be the number of complex critical points on this variety of

```math
f_U(X)=\mathop{\mathrm{tr}}\nolimits\bigl((X-U)^T(X-U)\bigr).
```

This is the complexification of squared real Frobenius distance; the transpose is not a conjugate transpose. Equivalently, count the solutions $`X`$ of $`X^TJX=J`$ and

```math
\mathop{\mathrm{tr}}\nolimits\bigl((U-X)^TXH\bigr)=0
\quad\text{for every }H\in\mathbb C^{2m\times2m}
\text{ satisfying }H^TJ+JH=0.
```

“Generic” means outside a proper Zariski-closed set where the finite critical-point count can change. Is

```math
D_m=2^{m^2}+2^{\,2m-1}
\qquad\text{for every }m\ge1?
```

## Relevance
 $`D_m`$ measures the algebraic complexity of finding the nearest real symplectic matrix. This is a structured matrix nearness problem, relevant when numerical approximations should preserve a symplectic form. The standard Frobenius inner product and the displayed $`J`$ are part of the problem.

## References

- J. A. Baaijens and J. Draisma, *Euclidean distance degrees of real algebraic groups*, Linear Algebra and its Applications 467 (2015), 174–187, §5, p.187: proposed formula immediately before Problem 5.1; §2 for critical equations ([version of record](https://pure.tue.nl/ws/files/3846347/391917266748824.pdf); [journal](https://doi.org/10.1016/j.laa.2014.11.012)).
- Z. Lai, L.-H. Lim, and K. Ye, *Euclidean Distance Degree in Manifold Optimization*, SIAM Journal on Optimization 35 (2025), 2402–2422, related ED-degree results for flag, Grassmann, and Stiefel models ([journal](https://doi.org/10.1137/25M1735032)).

## Status check — 2026-09-08
 The source computed $`D_1=4`$, $`D_2=24`$, and $`D_3=544`$, and explicitly proposed the displayed pattern. It did not assert a proof. Searches for “symplectic group”, “Euclidean distance degree”, “ED degree”, “544”, and 2024–2026 found no proof, counterexample, or additional general formula. The 2025 related article's abstract treats different manifold families. No recent explicit reaffirmation of this exact formula was located.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

## Audit update — 2026-09-10

Rechecked [Baaijens–Draisma](https://pure.tue.nl/ws/files/3846347/391917266748824.pdf), §5: the general expression is proposed from small-rank computations, without a proof. Searches for symplectic Euclidean distance degrees and subsequent matrix-manifold ED-degree work found no derivation of this formula. Importance is narrowed to specialist because the requested output is a specific algebraic degree, rather than a general symplectic projection algorithm.
