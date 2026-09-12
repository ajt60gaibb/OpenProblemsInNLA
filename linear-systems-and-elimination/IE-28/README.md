# IE-28 — Positive diagonal preconditioning with a nilpotent stiff limit

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Diagonal preconditioners for collocation systems  
**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** The problem is a uniform existence assertion for a positive diagonal solution of nonlinear spectral equations. It underlies parallel iteration for implicit Runge–Kutta and spectral deferred-correction methods.

## Statement

Let $`s\ge2`$ be an integer and $`0< c_1<\cdots< c_s\le1`$ be real collocation nodes. Let

```math
\ell_j(t)=\prod_{k\ne j}\frac{t-c_k}{c_j-c_k},
\qquad A_{ij}=\int_0^{c_i}\ell_j(t)\,dt,
\qquad A\in\mathbb R^{s\times s}.
```

**Conjecture (van der Houwen–de Swart).** For every such node set, does there exist a real positive diagonal matrix $`D=\mathop{\mathrm{diag}}\nolimits(d_1,\ldots,d_s)`$ such that

```math
\rho(I_s-D^{-1}A)=0?
```

Equivalently, require

```math
 (I_s-D^{-1}A)^s=0,
```

or the polynomial identity

```math
\det((1-t)D+tA)=\det D\qquad\text{for every }t\in\mathbb R.
```

No ordering constraint on the positive $`d_i`$ is imposed. The source states the conjecture for collocation-based Runge–Kutta correctors; the explicit positive-distinct-node quantification here is an editorial formalization of its collocation-matrix setting, also used by the 2025 treatment. The exclusion of a node at zero is essential: such a node gives $`A`$ a zero row and forces $`I_s-D^{-1}A`$ to have eigenvalue one. Rescaling positive nodes to $`c_s\le1`$ does not change the existence question.

## Numerical significance and known distinctions

For the diagonal-preconditioned iteration of a collocation system on the scalar test equation, the iteration matrix is

```math
K(z)=z(I_s-zD)^{-1}(A-D).
```

Its limit as $`|z|\to\infty`$ is $`I_s-D^{-1}A`$. The conjecture thus asks whether the stiff-limit iteration can terminate in at most $`s`$ steps using a positive diagonal preconditioner, which permits independent stage solves. It does not assert uniform contraction for finite $`z`$ or absence of transient nonnormal growth.

The case $`s=2`$ has an elementary verification. Write $`a=c_1< b=c_2`$ and choose

```math
d_1=\frac{a(2b-a)}{2(b-a)+\sqrt{2ab}},\qquad d_2=\frac{ab}{2d_1}.
```

Both entries are positive, and direct substitution gives
$`\mathop{\mathrm{tr}}\nolimits(D^{-1}A)=2`$ and $`\det(D^{-1}A)=1`$.
Cayley–Hamilton therefore gives $`(I_2-D^{-1}A)^2=0`$.
This verification is included here explicitly; it is not a claim of an
all-stage result in the cited papers.

The 2025 MIN-SR-S construction searches for this nilpotence through determinant equations, and explicitly leaves existence at arbitrary stage count unproved. Its theorem on nilpotence of $`A-D`$ concerns the nonstiff limit, a different matrix. Its variable-sweep MIN-SR-FLEX coefficients also do not supply one fixed $`D`$ solving the displayed target. Triangular preconditioners can achieve stiff-limit nilpotence by LU splitting, but do not meet the diagonal constraint.

## References and status check

- P. J. van der Houwen and J. J. B. de Swart, *Triangularly implicit iteration methods for ODE-IVP solvers*, SIAM Journal on Scientific Computing 18(1) (1997), 41–55. [DOI](https://doi.org/10.1137/S1064827595287456); [CWI PDF](https://ir.cwi.nl/pub/2191/2191D.pdf). §3.2.1, p.46, states the positive-diagonal zero-spectral-radius conjecture; §3.2.2, equation (3.9) and Theorem 3.1, specifies collocation matrices with positive distinct abscissas.
- G. Čaklović, T. Lunet, S. Götschel and D. Ruprecht, *Improving efficiency of parallel across the method spectral deferred corrections*, SIAM Journal on Scientific Computing 47(1) (2025), A430–A453. [DOI and full text](https://doi.org/10.1137/24M1649800); [open PDF](https://d-nb.info/1363153935/34). §2.2, equations (2.11)–(2.13), distinguishes the two limits; §2.2.3, p.A439, Definition 2.10 and equation (2.38), explicitly discusses unproved existence for arbitrary stage counts.

On 2026-09-11, checked both full papers, searched the original title and positive diagonal/nilpotent collocation conjecture, and searched MIN-SR-S existence, proofs and 2026 follow-ups. No theorem or counterexample settling this fixed-diagonal existence target was located. The 2025 paper gives current explicit evidence that the issue remains unresolved; its numerical optimization is not an all-node, all-stage existence proof. This is a bounded check. The target is distinct from the [LU-based spectral disk question](../IE-27/README.md) and from existing incomplete-factorization entries.
