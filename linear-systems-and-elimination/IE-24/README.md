# IE-24 — RILU conditioning for the Neumann problem on smooth planar domains

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-11-28

**Rating rationale:** Uniform cut-cell estimates on arbitrary smooth domains are challenging beyond rectangles; effective Neumann preconditioning has community importance.

## Statement

Let $`\Omega\subset\mathbb R^2`$ be a fixed bounded connected domain with smooth boundary. For grid width $`h>0`$, retain the points $`p\in h\mathbb Z^2`$ whose square control cells $`C_p=p+[-h/2,h/2]^2`$ intersect $`\Omega`$. Order them lexicographically and identify them with $`1,\ldots,N_h`$. For cells sharing a face, put

```math
w_{pq}=\frac{\mathop{\mathrm{length}}\nolimits(C_p\cap C_q\cap\Omega)}h,
```

and set other weights to zero. Define the Purvis–Burkhalter Neumann matrix by $`a_p=\sum_qw_{pq}`$, $`A_{pp}=a_p`$, and $`A_{pq}=-w_{pq}`$ for $`p\ne q`$. Write $`L`$ for its strictly lower triangular part.

For $`0< r<1`$, the source's relaxed incomplete LU preconditioner uses $`E=\mathop{\mathrm{diag}}\nolimits(e_1,\ldots,e_{N_h})`$, where $`e_1=a_1`$ and, in increasing order,

```math
e_p=a_p-\sum_{\substack{q< p\\w_{pq}>0}}
\frac{w_{pq}}{e_q}
\left(w_{pq}+(1-r)\sum_{\substack{s>q\\s\ne p}}w_{qs}\right),
\qquad M=(L+E)E^{-1}(E+L^T).
```

This is Definition 4 written with numbered grid points; sums contain only neighboring cells. Define $`\kappa_+(M^{-1}A)`$ as the largest divided by the smallest **positive** eigenvalue of $`M^{-1/2}AM^{-1/2}`$, excluding the Neumann zero eigenvalue.

**Conjecture.** There are constants $`c_\Omega,K_\Omega,h_\Omega>0`$, independent of $`h`$, such that with $`r=c_\Omega h^2`$, for all $`0< h< h_\Omega`$ the pivots are positive and

```math
\kappa_+(M^{-1}A)\le K_\Omega h^{-1}.
```

Here $`h_\Omega`$ is small enough that $`r<1`$. This makes the source's “some moderate constant” explicit as an existence quantifier; no numerical meaning is assigned to “moderate.” The authors recommend $`c_\Omega=1`$ in practice.

## Numerical significance

This asks whether a specified sparse preconditioner gives the observed improvement in conditioning for general curved Neumann boundaries. The source proves the rectangular case, while its three-dimensional experiments do not support the same RILU claim.

## Positive pivots and a uniform lower spectral bound

**Partial result (AI-derived).** On every smooth domain in the statement,
the RILU pivots are positive for sufficiently small $`h`$ and every
$`0< r<1`$. For $`r=c h^2`$ with any fixed $`c>0`$, the smallest positive
generalized eigenvalue stays bounded away from zero uniformly in $`h`$.
The upper spectral bound needed for the conjectured condition number
remains open.

**Pivots.** The positive-weight face graph is connected. Each retained
cell has an interior point in $`\Omega`$ by openness. A polygonal path
in $`\Omega`$ between two such points can be perturbed to avoid the
grid faces of codimension at least two. Its face crossings then give
a chain of positive weights. For small $`h`$ there is a cell with two
forward neighbors of weight one, by choosing a grid stencil inside a
ball contained in $`\Omega`$.

Orient each positive-weight edge forward in the ordering. Put
$`s_p=\sum_{q>p}w_{pq}`$ and $`k_p=e_p-s_p`$. The recurrence gives

```math
k_1=0,\qquad
k_p=\sum_{q< p,\,w_{pq}>0}\frac{w_{pq}}{e_q}
       \bigl(k_q+r(s_q-w_{pq})\bigr).
```

Inductively $`k_p\ge0`$, so a vertex with a forward edge has $`e_p>0`$.
For a sink, consider it and all its directed ancestors. If no ancestor
has two forward neighbors, each ancestor other than the sink has its
only forward neighbor in this set. Any edge entering the set would
make its starting vertex an ancestor. The set would then have no
undirected edge to its complement. Connectedness would make it the
whole graph, contrary to the interior stencil. A branch at an
ancestor thus gives a strictly positive term on the first edge of
a path to the sink. The recurrence propagates this positivity along
the path and gives positive pivot at the sink too.

### Weighted Poincaré estimate for the cut-cell graph

The estimate below holds in both dimensions two and three with the
face fractions in [IE-25](../IE-25/README.md). For some $`C_\Omega`$
and all sufficiently small $`h`$, every array of grid values satisfies

```math
\min_{b\in\mathbb R}\sum_p a_p|x_p-b|^2\le C_\Omega h^{-2}x^TAx.
```

For the boundary estimate, use a finite cover of the smooth boundary
by graph charts with a coordinate axis directed inward. Such an axis
exists at every boundary point because some coordinate component of its
normal is nonzero. Reflect that coordinate when necessary and write the
section of the domain as $`x_d< f(x')`$ with Lipschitz constant $`L`$
bounded uniformly over the charts. Call a center deep if it lies in
$`\Omega`$ at distance greater than $`4\sqrt d\,h`$ from its boundary.
For small $`h`$ each remaining retained cell and a bounded number of
its neighboring cells along the inward axis fit in one chart, by
compactness and by taking the initial charts slightly smaller than
their graph neighborhoods.

In such a cell, let $`W_0`$ be the fraction of its inward face in
$`\Omega`$. The opposite face fraction is at most $`W_0`$. On a side
face, fix the other tangential coordinates and let $`\ell`$ be the
vertical length in $`\Omega`$ at those coordinates. Moving from
the side into the full tangential footprint by at most
$`\ell/(2\max\{1,L\})`$ keeps the graph strictly above the inward
face height when $`\ell>0`$. Integrating over the other tangential
coordinates shows that the side face fraction is at most
$`2\max\{1,L\}W_0`$. Summing the faces gives $`W_0\ge c_0a_p`$
for a uniform $`c_0>0`$.

Moving along the inward axis keeps the same tangential footprint and
moves the face height down, so the successive face fractions are
nondecreasing. After a uniformly bounded number of steps the center
is deep. Indeed the initial excess of its height above $`f`$ at the
tangential center is $`O(h)`$ since the cell meets $`\Omega`$, and
a vertical depth $`s>0`$ below a Lipschitz graph gives distance at
least $`s/\sqrt{1+L^2}`$ from that graph. For small $`h`$ any nearest
boundary point remains in the chart over the bounded path. Each path
therefore joins the original center to a deep center $`p_*`$ along
edges of weight at least $`c_0a_p`$. Each edge and each deep endpoint
are used by only a bounded number of these paths, since all paths
have bounded length in grid steps. Cauchy–Schwarz along the paths gives

```math
\sum_{p\ \mathrm{not\ deep}}a_p|x_p-x_{p_*}|^2\le C x^TAx.
```

For the deep values, interpolate the nodal values by multilinear grid
interpolation on the inner offset of $`\Omega`$ at distance
$`2\sqrt d\,h`$ from the boundary. The interpolation cubes that meet
this offset have fully interior nodal control cells. Local scaling on
the cubes and the unit weights of their lattice edges bound the
integral of the squared gradient by $`C h^{d-2}x^TAx`$.
The smooth boundary has a tubular neighborhood. Moving its boundary
inward by $`2\sqrt d\,h`$ inside this neighborhood with a fixed smooth
cutoff gives uniformly bi-Lipschitz maps from $`\Omega`$ to the inner
offsets for small $`h`$. Thus the continuum Poincaré constant on the
inner offset is uniform. With $`b`$ the mean of the interpolant there,
the integral of the squared difference from $`b`$ is at most
$`C h^{d-2}x^TAx`$. Each deep center is the lower lattice vertex of a
distinct interpolation cube entirely inside this offset. On a cube
the squared nodal value times $`h^d`$ is controlled by the squared
$`L^2`$ norm of the interpolant by finite-dimensional norm
equivalence on the unit cube. Consequently the deep squared nodal
differences from $`b`$ sum to at most $`C h^{-2}x^TAx`$.
Combine this with the path estimate, bounded endpoint congestion, and
$`a_p\le2d`$ to obtain the claimed weighted inequality.

**Generalized eigenvalues.** Expansion of the factors gives
$`M=A+\mathop{\mathrm{diag}}\nolimits(M\mathbf1)-L_F`$, where $`L_F`$ is the
positive semidefinite graph Laplacian with off-diagonal fill weights
$`F_{ps}=\sum_{q<\min(p,s)} w_{pq}w_{sq}/e_q`$ for $`p\ne s`$.
The RILU recurrence gives the row sums

```math
0\le (M\mathbf1)_p=r\sum_{q< p,\,w_{pq}>0}
       \frac{w_{pq}(s_q-w_{pq})}{e_q}\le r a_p,
```

using $`e_q\ge s_q`$. On the $`M`$-orthogonal complement of the
constant vector, $`x^TMx\le (x-b\mathbf1)^T M(x-b\mathbf1)`$ for
every constant $`b`$. Choose $`b`$ by the weighted Poincaré estimate.
The factor identity and $`r=c h^2`$ give
$`x^TMx\le (1+cC_\Omega)x^TAx`$. The graph has just the constants
in its kernel and $`M`$ is positive definite by the pivot result.
The generalized Rayleigh principle gives
$`\lambda_{\min,+}(M^{-1}A)\ge(1+c C_\Omega)^{-1}`$.

## References and status check

- B. Lee and C. Min, *Optimal preconditioners on solving the Poisson equation with Neumann boundary conditions*, J. Comput. Phys. **433** (2021), 110189, [DOI](https://doi.org/10.1016/j.jcp.2021.110189). [Author text](https://math.ewha.ac.kr/~chohong/publications/article_49_copy.pdf): §2.1, equation (3); §3, Definition 4 and the conjecture, pp. 4–5; §5 gives the rectangular-domain result.
- G. Hwang et al., *Localized Estimation of Condition Numbers for MILU Preconditioners on a Graph*, SIAM J. Numer. Anal. **64** (2026), 1443–1477, [DOI](https://doi.org/10.1137/24M1722134); [available preprint](https://arxiv.org/abs/2501.00245), §2.1 and §5, p. 21: assumes positive definite matrices and leaves Neumann conditions to future work.

On 2026-09-10, checked the full 2021 author text, the later available MILU preprint, its 2026 publication record, and targeted RILU/Neumann/title searches including 2025–2026. No general-domain proof or counterexample was located. The 2026 journal full text was not available; the later-source comparison uses its primary abstract and author preprint.

## Independent audit — 2026-09-10

The recurrence and smooth-domain quantifiers were independently compared with Lee–Min, Definition 4 and the §3 conjecture. The §5 proof treats rectangles, whose corners exclude them from the displayed smooth-boundary class; it therefore does not justify a partial-resolution label for this exact target. The full author PDF and the later MILU preprint were checked. The latter assumes positive definiteness in §2.1 and leaves Neumann conditions to future work in §5. Targeted subsequent searches found no smooth-domain resolution.
