# IE-25 — Perturbed MILU conditioning for Neumann problems in two and three dimensions

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-11-28

**Rating rationale:** Controlling the perturbed factorization uniformly for singular Neumann systems in two and three dimensions is challenging. Community impact comes from a concrete preconditioner for widely used PDE linear solves.

## Statement

Fix $`d\in\{2,3\}`$ and a bounded connected smooth domain $`\Omega\subset\mathbb R^d`$. On $`h\mathbb Z^d`$, retain points whose cubic control cells $`C_p=p+[-h/2,h/2]^d`$ intersect $`\Omega`$, ordered lexicographically as $`1,\ldots,N_h`$. For face neighbors set

```math
w_{pq}=\frac{\mathop{\mathrm{vol}}\nolimits_{d-1}(C_p\cap C_q\cap\Omega)}{h^{d-1}},
```

and set other weights to zero. Let $`a_p=\sum_qw_{pq}`$, $`A_{pp}=a_p`$, $`A_{pq}=-w_{pq}`$ for $`p\ne q`$, and let $`L`$ be the strictly lower triangular part of $`A`$. This is the Purvis–Burkhalter Neumann discretization, with length fractions in two dimensions and face-area fractions in three dimensions.

For $`\varepsilon>0`$, define $`E=\mathop{\mathrm{diag}}\nolimits(e_1,\ldots,e_{N_h})`$ recursively by

```math
e_1=a_1,\qquad
e_p=(1+\varepsilon)a_p-
\sum_{\substack{q< p\\w_{pq}>0}}
\frac{w_{pq}}{e_q}\sum_{s>q}w_{qs}\quad(p>1),
```

and $`M=(L+E)E^{-1}(E+L^T)`$. This expresses the source's PMILU recurrence by neighbor sums, including its explicitly unperturbed first pivot. Its two-dimensional display is Definition 5; §4 states the conjecture in both dimensions.

When the pivots are positive, let $`\kappa_+(M^{-1}A)`$ be the ratio of the largest to smallest positive eigenvalue of $`M^{-1/2}AM^{-1/2}`$; the zero eigenvalue from the Neumann nullspace is excluded.

**Conjecture.** There exist $`c_\Omega,K_\Omega,h_\Omega>0`$, independent of $`h`$, such that choosing $`\varepsilon=c_\Omega h^2`$ gives positive pivots and

```math
\kappa_+(M^{-1}A)\le K_\Omega h^{-1}
\qquad(0< h< h_\Omega).
```

The existence quantifier spells out the source's choice of “some moderate constant”; it does not impose an invented interval for that constant. The authors suggest the practical choice $`c_\Omega=1`$.

## Numerical significance

The question concerns a concrete diagonal perturbation of incomplete factorization for singular Neumann systems. It is separate from relaxed ILU: the diagonal recurrence differs, and the proposed PMILU bound includes three dimensions.

## Positive pivots and a uniform lower spectral bound

**Partial result (AI-derived).** In both dimensions of the statement,
the PMILU pivots are positive for all $`\varepsilon>0`$ and sufficiently
small $`h`$. For $`\varepsilon=ch^2`$ with any fixed $`c>0`$, the
smallest positive generalized eigenvalue stays bounded away from zero
uniformly in $`h`$. The upper spectral bound needed for the conjectured
condition number remains open.

The positive-weight face graph is connected and has more than one
vertex for small $`h`$. The path proof and the [weighted Poincaré estimate](../IE-24/README.md#weighted-poincaré-estimate-for-the-cut-cell-graph)
apply to the stated square or cubic control cells. Put
$`s_p=\sum_{q>p}w_{pq}`$ and $`k_p=e_p-s_p`$. The unperturbed first
pivot is $`e_1=s_1=a_1>0`$, so $`k_1=0`$. For $`p>1`$ the PMILU
recurrence gives

```math
k_p=\varepsilon a_p+\sum_{q< p,\,w_{pq}>0}\frac{w_{pq}}{e_q}k_q.
```

Since $`a_p>0`$ at every vertex of this connected graph, induction
gives $`k_p>0`$ for all $`p>1`$ and positive pivots throughout.

Expanding the factors gives $`M=A+\mathop{\mathrm{diag}}\nolimits(M\mathbf1)-L_F`$,
where $`L_F`$ is the graph Laplacian with nonnegative fill weights
$`F_{ps}=\sum_{q<\min(p,s)}w_{pq}w_{sq}/e_q`$ for $`p\ne s`$.
The row sums are $`(M\mathbf1)_1=0`$ and
$`(M\mathbf1)_p=\varepsilon a_p`$ for $`p>1`$. The exception is
exactly the unperturbed first pivot in the displayed recurrence.
The row sums follow by subtracting $`a_p`$ from $`e_p`$ and adding
$`\sum_{q< p,\,w_{pq}>0}w_{pq}s_q/e_q`$.

For $`x`$ in the $`M`$-orthogonal complement of the constants,
$`x^TMx\le (x-b\mathbf1)^TM(x-b\mathbf1)`$ for every constant
$`b`$. Choose $`b`$ minimizing $`\sum_p a_p|x_p-b|^2`$. The fill
Laplacian is positive semidefinite and $`A\mathbf1=0`$, so the
factor identity and the weighted Poincaré estimate give

```math
x^TMx\le x^TAx+\varepsilon \sum_p a_p|x_p-b|^2
      \le (1+cC_\Omega)x^TAx.
```

The generalized Rayleigh principle yields
$`\lambda_{\min,+}(M^{-1}A)\ge(1+cC_\Omega)^{-1}`$.

## References and status check

- B. Lee and C. Min, *Optimal preconditioners on solving the Poisson equation with Neumann boundary conditions*, J. Comput. Phys. **433** (2021), 110189, [DOI](https://doi.org/10.1016/j.jcp.2021.110189). [Author text](https://math.ewha.ac.kr/~chohong/publications/article_49_copy.pdf): §2.1, equation (3); §4, Definition 5 and conjecture, pp. 5–6; §6.2 for the three-dimensional experiments.
- G. Hwang et al., *Localized Estimation of Condition Numbers for MILU Preconditioners on a Graph*, SIAM J. Numer. Anal. **64** (2026), 1443–1477, [DOI](https://doi.org/10.1137/24M1722134); [available preprint](https://arxiv.org/abs/2501.00245), §2.1 and §5, p. 21.

On 2026-09-10, checked the original full author text, the later preprint's positive-definite assumptions and explicit Neumann future-work statement, its 2026 publication record, and targeted PMILU/Neumann/title searches including 2025–2026. No resolution was found. The 2026 journal full text was unavailable; this is a bounded check using its primary abstract and author preprint. The source's descriptive phrase “MILU of $`A+\varepsilon D`$” differs at the first pivot from its displayed Definition 5; this entry follows the display.

## Independent audit — 2026-09-10

Definition 5 and the §4 conjecture in the full Lee–Min author PDF support the displayed PMILU recurrence, including the first-pivot exception. The paper proves the rectangular RILU result, not a PMILU theorem; its smooth-domain PMILU evidence is numerical. The positive-definite assumptions and Neumann future-work boundary of the later preprint were checked, along with targeted subsequent searches. No exact proved subfamily warranting a partial-resolution label, or general resolution, was located.
