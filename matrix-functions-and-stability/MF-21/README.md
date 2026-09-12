# MF-21 — The uniform expansion threshold for Toeplitz symbols with higher-order zeros

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-12

**Rating rationale:** Matching bulk asymptotics with extreme eigenvalues at the exact breakdown order is challenging; the detailed expansion threshold is mainly important to structured spectral specialists.

## Affirmative resolution - 12 September 2026 (UTC)

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

[Theorem 1 and Sections 2-5 of the complete proof](solution.md) establish all three assertions below for every integer $`m\ge3`$, using the same smooth coefficient functions with $`d_0=g_m`$. The expansion is uniform over every eigenvalue through order $`2m-1`$, extends to order $`2m`$ above the stated logarithmic-squared index cutoff, and fails to extend uniformly to all indices at that order. The matrix, grid normalization, parameter quantifiers and cutoff are unchanged.

[Proof PDF](solution.pdf) · [Standalone proof TeX](solution.tex) · [Independent mathematical review](../../references/stepaniants-mf21-2026-09-12/independent-review.md) · [Submission and public-source audit](../../references/stepaniants-mf21-2026-09-12/README.md).

The complete proof passed a separate Codex-agent informal audit. It derives the bulk expansion from an exact boundary determinant and proves the final obstruction using a classical uniform inverse-kernel limit and a trace identity. Barrera, Böttcher, Grudsky, Maximenko and the cited later authors retain credit for the conjecture and prior cases; Böttcher-Widom and their cited predecessors retain credit for the inverse-kernel theorem. Substantial AI assistance is disclosed. This is neither external human peer review nor formal verification. The original statement, permanent ID, references and dated history are retained below; the ratings are historical.

## Statement

For each integer $`m\ge3`$, let

```math
g_m(\theta)=\bigl(2\sin(\theta/2)\bigr)^{2m},\qquad
\widehat g_{m,k}=\frac1{2\pi}\int_{-\pi}^{\pi}g_m(\theta)e^{-ik\theta}\,d\theta.
```

Let $`T_n(g_m)=(\widehat g_{m,j-k})_{j,k=1}^n`$, with eigenvalues $`\lambda_{n,1}\le\cdots\le\lambda_{n,n}`$ counted with multiplicity. For real continuous functions $`d_0,\ldots,d_{2m}`$ on $`[0,\pi]`$, independent of $`n,j`$, write

```math
R_{p,n,j}=\lambda_{n,j}-\sum_{k=0}^p
\frac{d_k(j\pi/(n+2))}{(n+2)^k}.
```

**Conjecture 8.4 of Barrera–Böttcher–Grudsky–Maximenko.** Such coefficient functions exist, with $`d_0=g_m`$, for which all three assertions hold:

1. For every integer $`0\le p\le2m-1`$, there are constants $`D_p>0`$ and $`N_p\in\mathbb N`$ such that

   $`\displaystyle |R_{p,n,j}|\le D_p(n+2)^{-p-1}\qquad(n\ge N_p,\ 1\le j\le n).`$

2. There are constants $`D_{2m}>0`$ and $`N_{2m}\in\mathbb N`$ such that

   $`\displaystyle |R_{2m,n,j}|\le D_{2m}(n+2)^{-2m-1}`$

   whenever $`n\ge N_{2m}`$ and $`\lceil(\log(n+2))^2\rceil\le j\le n`$.
3. No constants $`D>0,N\in\mathbb N`$ make the bound $`|R_{2m,n,j}|\le D(n+2)^{-2m-1}`$ valid for every $`n\ge N`$ and every $`1\le j\le n`$.

All constants may depend on $`m`$ and the expansion order; $`\log`$ denotes the natural logarithm. The same coefficient functions are used throughout. The continuity and existence quantifiers make explicit the regular-expansion convention of the source's Theorem 1.2 and §8; these are not matrix-size-dependent fitted coefficients.

## Numerical significance

Regular eigenvalue expansions support accurate computation without forming large Toeplitz matrices. This conjecture identifies exactly where extreme eigenvalues obstruct a uniform expansion for these polynomial symbols. It retains all three parts as one problem.

## References and status check

- M. Barrera, A. Böttcher, S. M. Grudsky and E. A. Maximenko, *Eigenvalues of even very nice Toeplitz matrices can be unexpectedly erratic*, Oper. Theory Adv. Appl. **268** (2018), 51–77, [DOI](https://doi.org/10.1007/978-3-319-75996-8_2); [author preprint](https://arxiv.org/abs/1710.05243), Conjecture 8.4, p. 26, equation (8.4); Theorem 1.2 supplies the proved $`m=2`$ analogue.
- M. Barrera, S. Grudsky, V. Stukopin and I. Voronin, *Asymptotics of the eigenvalues of seven-diagonal Toeplitz matrices of a special form*, Adv. Oper. Theory **9** (2024), 79, [DOI](https://doi.org/10.1007/s43036-024-00374-1); [preprint](https://arxiv.org/abs/2111.07196), Theorems 2.3–2.6. This studies the sixth-order-zero case with more elaborate formulas.
- A. Böttcher, *Ten years with Sergei Grudsky in the eigenvalue bulk of Toeplitz matrices*, J. Math. Sci. **298** (2026), 363–376, [DOI](https://doi.org/10.1007/s10958-025-07833-x), section “Beyond the simple-loop class,” Theorems 2–5 and discussion of higher-order zeros.

On 2026-09-10, checked the original full preprint, the seven-diagonal follow-up's full preprint and publication record, the 2026 survey, and targeted title/conjecture/2025–2026 searches. No resolution of all parts for every $`m\ge3`$ was located. Later local second-order expansions and results confined to $`m=3`$ do not establish this full statement. This bounded search is not a proof of openness.

## Audit — 2026-09-10

Independently rechecked [Conjecture 8.4](https://arxiv.org/pdf/1710.05243), [the seven-diagonal paper's Theorems 2.3–2.6](https://arxiv.org/pdf/2111.07196), and [Böttcher's survey](https://doi.org/10.1007/s10958-025-07833-x). Corrected the status to Open: the proved $`m=2`$ analogue lies outside the displayed range, and the $`m=3`$ local and second-order formulas do not establish the three-part threshold assertion. The [March 2026 eigenvalue-superposition paper](https://doi.org/10.1007/s10958-026-08227-3) assumes simple-loop symbols, excluding these higher-order zeros. Title and conjecture searches found no complete resolution. Challenging difficulty and specialist importance are retained.

## Resolution audit - 2026-09-12

The independent audit checked the complete all-$`m`$ argument, including the coalescing characteristic roots, normalized determinant remainder, upper-endpoint cancellation, eigenvalue indexing, all three expansion orders, and dominated trace limit. The primary-source and public branch/fork/PR checks found no existing full resolution at the recorded time; the linked submission record gives the precise scope and limitations of that search.
