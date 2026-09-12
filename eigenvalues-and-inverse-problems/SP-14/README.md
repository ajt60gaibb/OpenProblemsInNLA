# SP-14 — Widom's canonical distribution conjecture for Toeplitz eigenvalues

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Nonnormal Toeplitz eigenvalue asymptotics  
**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** A general theorem must distinguish symbols whose Toeplitz spectra follow their values from the markedly different behavior of analytic symbols. This is a longstanding obstacle in the spectral analysis of nonnormal structured matrices.

## Statement

Let $`\mathbb T=\{z\in\mathbb C:|z|=1\}`$ and $`a\in C(\mathbb T;\mathbb C)`$. Define

```math
a_k=\frac1{2\pi}\int_0^{2\pi}a(e^{it})e^{-ikt}\,dt,
\qquad T_n(a)=(a_{j-k})_{j,k=0}^{n-1}.
```

Say that $`a`$ extends analytically to an inner annulus if, for some $`0<r<1`$, there is a holomorphic function on $`r<|z|<1`$ extending continuously to $`|z|=1`$ with boundary value $`a`$. Define extension to an outer annulus analogously using $`1<|z|<R`$ for some $`R>1`$.

**Conjecture (Widom).** If $`a`$ has neither such inner nor such outer extension, then for every continuous compactly supported $`F:\mathbb C\to\mathbb C`$,

```math
\lim_{n\to\infty}\frac1n\sum_{j=1}^n F(\lambda_j(T_n(a)))
=\frac1{2\pi}\int_0^{2\pi}F(a(e^{it}))\,dt.
```

Eigenvalues are counted with algebraic multiplicity. This conclusion is called *canonical eigenvalue distribution*. The conjecture asserts that failure requires a one-sided analytic extension; it does not assert failure for every symbol that has one.

## Known cases and numerical significance

Canonical distribution holds for real-valued symbols and for the Tilli class, whose essential range has empty interior and connected complement. Widom also proved cases with nonsmooth symbols tracing Jordan curves. The general continuous-symbol assertion remains the target.

Toeplitz singular-value distributions are much better understood than their nonnormal eigenvalue counterparts. This question determines when sampling the symbol predicts the bulk eigenvalues, a basic issue for structured eigensolvers. It is distinct from [SP-06](../SP-06/README.md), which asks for real spectra in every finite order, and from individual-eigenvalue expansion problems.

## References and status check

- H. Widom, *Eigenvalue distribution of nonselfadjoint Toeplitz matrices and the asymptotics of Toeplitz determinants in the case of nonvanishing index*, Operator Theory: Advances and Applications 48 (1990), 387–421. Historical originating source, as identified by the explicit restatements below.
- J. M. Bogoya, A. Böttcher and S. M. Grudsky, *Asymptotics of individual eigenvalues of a class of large Hessenberg Toeplitz matrices*, OTAA 220 (2012), 77–95. [Author manuscript](https://www.math.cinvestav.mx/~grudsky/Papers/116.pdf), §1, p.2 after (1.1), states the annulus conjecture explicitly.
- M. Bogoya, S.-E. Ekström, S. Serra-Capizzano and P. Vassalos, *Matrix-less methods for the spectral approximation of large non-Hermitian Toeplitz matrices: A concise theoretical analysis and a numerical study*, Numerical Linear Algebra with Applications 31 (2024), e2545. [DOI](https://doi.org/10.1002/nla.2545); [institutional PDF](https://uu.diva-portal.org/smash/get/diva2%3A1824576/FULLTEXT01.pdf). The introduction before Theorem 1 reaffirms the conjecture and states the Tilli-class result.

On 2026-09-11, checked the explicit source statements and searched Widom, canonical distribution, analytic annuli, and nonselfadjoint Toeplitz proof/counterexample combinations, including 2025–2026 results. No full resolution was found. Other conjectures bearing Widom's name, about determinant or trace asymptotics, do not settle this eigenvalue-distribution statement. This is a bounded status check.
