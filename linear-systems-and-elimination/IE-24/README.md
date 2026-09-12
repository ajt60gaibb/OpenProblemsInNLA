# IE-24 — RILU conditioning for the Neumann problem on smooth planar domains

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-10

**Rating rationale:** Uniform cut-cell estimates on arbitrary smooth domains are challenging beyond rectangles; effective Neumann preconditioning has community importance.

## Statement

Let $`\Omega\subset\mathbb R^2`$ be a fixed bounded connected domain with smooth boundary. For grid width $`h>0`$, retain the points $`p\in h\mathbb Z^2`$ whose square control cells $`C_p=p+[-h/2,h/2]^2`$ intersect $`\Omega`$. Order them lexicographically and identify them with $`1,\ldots,N_h`$. For cells sharing a face, put

```math
w_{pq}=\frac{\mathop{\mathrm{length}}\nolimits(C_p\cap C_q\cap\Omega)}h,
```

and set other weights to zero. Define the Purvis–Burkhalter Neumann matrix by $`a_p=\sum_qw_{pq}`$, $`A_{pp}=a_p`$, and $`A_{pq}=-w_{pq}`$ for $`p\ne q`$. Write $`L`$ for its strictly lower triangular part.

For $`0<r<1`$, the source's relaxed incomplete LU preconditioner uses $`E=\mathop{\mathrm{diag}}\nolimits(e_1,\ldots,e_{N_h})`$, where $`e_1=a_1`$ and, in increasing order,

```math
e_p=a_p-\sum_{\substack{q<p\\w_{pq}>0}}
\frac{w_{pq}}{e_q}
\left(w_{pq}+(1-r)\sum_{\substack{s>q\\s\ne p}}w_{qs}\right),
\qquad M=(L+E)E^{-1}(E+L^T).
```

This is Definition 4 written with numbered grid points; sums contain only neighboring cells. Define $`\kappa_+(M^{-1}A)`$ as the largest divided by the smallest **positive** eigenvalue of $`M^{-1/2}AM^{-1/2}`$, excluding the Neumann zero eigenvalue.

**Conjecture.** There are constants $`c_\Omega,K_\Omega,h_\Omega>0`$, independent of $`h`$, such that with $`r=c_\Omega h^2`$, for all $`0<h<h_\Omega`$ the pivots are positive and

```math
\kappa_+(M^{-1}A)\le K_\Omega h^{-1}.
```

Here $`h_\Omega`$ is small enough that $`r<1`$. This makes the source's “some moderate constant” explicit as an existence quantifier; no numerical meaning is assigned to “moderate.” The authors recommend $`c_\Omega=1`$ in practice.

## Numerical significance

This asks whether a specified sparse preconditioner gives the observed improvement in conditioning for general curved Neumann boundaries. The source proves the rectangular case, while its three-dimensional experiments do not support the same RILU claim.

## References and status check

- B. Lee and C. Min, *Optimal preconditioners on solving the Poisson equation with Neumann boundary conditions*, J. Comput. Phys. **433** (2021), 110189, [DOI](https://doi.org/10.1016/j.jcp.2021.110189). [Author text](https://math.ewha.ac.kr/~chohong/publications/article_49_copy.pdf): §2.1, equation (3); §3, Definition 4 and the conjecture, pp. 4–5; §5 gives the rectangular-domain result.
- G. Hwang et al., *Localized Estimation of Condition Numbers for MILU Preconditioners on a Graph*, SIAM J. Numer. Anal. **64** (2026), 1443–1477, [DOI](https://doi.org/10.1137/24M1722134); [available preprint](https://arxiv.org/abs/2501.00245), §2.1 and §5, p. 21: assumes positive definite matrices and leaves Neumann conditions to future work.

On 2026-09-10, checked the full 2021 author text, the later available MILU preprint, its 2026 publication record, and targeted RILU/Neumann/title searches including 2025–2026. No general-domain proof or counterexample was located. The 2026 journal full text was not available; the later-source comparison uses its primary abstract and author preprint.

## Independent audit — 2026-09-10

The recurrence and smooth-domain quantifiers were independently compared with Lee–Min, Definition 4 and the §3 conjecture. The §5 proof treats rectangles, whose corners exclude them from the displayed smooth-boundary class; it therefore does not justify a partial-resolution label for this exact target. The full author PDF and the later MILU preprint were checked. The latter assumes positive definiteness in §2.1 and leaves Neumann conditions to future work in §5. Targeted subsequent searches found no smooth-domain resolution.
