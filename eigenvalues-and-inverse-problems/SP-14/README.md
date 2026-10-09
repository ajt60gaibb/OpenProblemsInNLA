# SP-14 — Widom's canonical distribution conjecture for Toeplitz eigenvalues

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Nonnormal Toeplitz eigenvalue asymptotics  
**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Solved  
**Last checked:** 2026-10-09

**Rating rationale:** A general theorem must distinguish symbols whose Toeplitz spectra follow their values from the markedly different behavior of analytic symbols. This is a longstanding obstacle in the spectral analysis of nonnormal structured matrices. The ratings above are historical: the displayed conjecture is refuted below, and the earlier partial results and literature checks are retained.

## Resolution — 9 October 2026

**Negative resolution by Clemens Thalhammer**, Seminar for Applied Mathematics, ETH Zurich. [Standalone proof (PDF)](references/thalhammer-2026-10-09/counterexample.pdf) · [LaTeX](references/thalhammer-2026-10-09/counterexample.tex). **Theorem 6.1.**

There is a continuous symbol $`a`$ on $`\mathbb T`$ with neither an inner nor an outer annular analytic extension, and an increasing sequence $`n_j`$, such that $`T_{n_j}(a)`$ has both $`1`$ and $`-1`$ as eigenvalues of algebraic multiplicity at least $`\lfloor\theta(n_j-1)/2\rfloor`$, $`\theta=2^{-10000}`$, while both points lie outside $`a(\mathbb T)`$. For the continuous compactly supported test function $`\Phi(w)=\max\{0,\,1-8|w-1|\}`$ the right-hand side of the displayed limit is $`0`$ and the left-hand side is at least $`\theta/2`$ along $`n_j`$, so the conjectured limit fails.

The symbol is $`a(z)=z\,g(z^2)`$ with $`g(s)=\sqrt{1+s^{-1}}+P_-(s)+P_+(s)`$. The base symbol $`a_0(z)=\sqrt{z^2+1}`$ traces the lemniscate $`|w^2-1|=1`$, a figure-eight through the origin, and $`T_{2m+1}(a_0)`$ has characteristic polynomial $`w(w^2-1)^m`$ exactly; $`a_0`$ itself has an outer extension. Positive Fourier packets $`\tau_js^{m_{j-1}}(1+s)`$ with $`\tau_j=\kappa\,2^{-\lceil\sqrt{2m_{j-1}+1}\rceil}`$ remove the outer extension; finitely many corrections of the coefficients $`g_{-m_j},\dots,g_{-5m_j/8-1}`$, each with an invisible endpoint-restoring packet, recreate the factor $`(w^2-1)^{\lfloor\theta m_j\rfloor}`$ in the characteristic polynomial of $`T_{2m_j+1}(a)`$, and the untouched coefficients $`g_{-3m_j}=\binom{1/2}{3m_j}`$ remove the inner extension. Later stages change no entry of an earlier selected section. The corrections exist by a quantitative implicit-function argument in a conformal spectral coordinate (Sections 2–5) and are fixed by a deterministic certificate search (Section 6).

**Comparison with the target.** The statement above quantifies over every continuous symbol with both extensions absent and over every continuous compactly supported $`F`$, with algebraic multiplicities. One such symbol and one such $`F`$ with a non-canonical limit refute it. The range is not a Jordan curve, so Widom's Jordan-curve theorem, Tilli's theorem and the Jordan-range subsequence result of 13 September 2026 below are untouched and consistent. The conjecture as stated here, in Bogoya–Böttcher–Grudsky 2012 §1, and in two further secondary sources carries no Jordan-curve hypothesis; Widom's 1990 text was not consulted.

**Verification status.** An [independent informal AI-agent review](references/thalhammer-2026-10-09/verification/independent-review-2026-10-09.md) (Claude, Anthropic, 9 October 2026, separate from the sessions that produced the argument) returned **PASS**: every finite identity was verified exactly, the construction was reproduced end to end at a small order in 60-digit arithmetic, the two central analytic estimates were confirmed numerically up to order 8192, and the logical chain and both external citations were audited. The review did not recompute the explicit constant ledger and did not re-prove the two-level isomorphism and far-factor derivative propositions line by line. The argument was developed with substantial AI assistance in ChatGPT (OpenAI) sessions directed by the author. This is not external human peer review, and no Lean verification was performed. [Submission record and reproduction](references/thalhammer-2026-10-09/README.md).

## Reviewed continuation — 13 September 2026

Sidney Holden (Center for Computational Biology, Flatiron Institute, Simons Foundation) supplies an inverse-corner criterion for one-sided annular extension and determinant limsup results. For continuous symbols with Jordan-curve range and winding $`+1`$ (respectively $`-1`$), absence of inner (respectively outer) extension yields a canonically distributed subsequence of the actual unperturbed Toeplitz eigenvalue measures; see the [seventh-round report](../../references/holden-continuations-2026-09-13/SP-14/report.pdf), Theorem 2.5, Theorem 3.1 and Corollary 4.5. The Jordan-curve argument includes positive-area curves.

Status remains **Partially resolved**: subsequence convergence does not establish the displayed full-sequence conclusion, and the unrestricted continuous-symbol case remains unresolved.

The [independent informal Codex AI-agent review](../../references/holden-continuations-2026-09-13/verification/SP-14/review.md) records its accepted scope and checks. [Submission, original package, reproduction and verified affiliation](../../references/holden-continuations-2026-09-13/README.md). This is not external human peer review or formal verification; no Lean verification was performed.


## Statement

Let $`\mathbb T=\{z\in\mathbb C:|z|=1\}`$ and $`a\in C(\mathbb T;\mathbb C)`$. Define

```math
a_k=\frac1{2\pi}\int_0^{2\pi}a(e^{it})e^{-ikt}\,dt,
\qquad T_n(a)=(a_{j-k})_{j,k=0}^{n-1}.
```

Say that $`a`$ extends analytically to an inner annulus if, for some $`0< r<1`$, there is a holomorphic function on $`r<|z|<1`$ extending continuously to $`|z|=1`$ with boundary value $`a`$. Define extension to an outer annulus analogously using $`1<|z|< R`$ for some $`R>1`$.

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
