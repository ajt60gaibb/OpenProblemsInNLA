# FR-10 — Sharp sampling complexity for Walsh restricted isometries

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** Closing the uniform logarithmic sampling gap is a longstanding restricted-isometry barrier comparable in scale to the cyclic Fourier problem, with consequences for sparse recovery and fast sketches.


<!-- colbrook-frames -->
## Reviewed submission - 2026-09-11

Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge.

Theorem 1 proves $`m_*(2^d,k)/d\to C_k`$ for $`k=2,3,4`$, with $`C_2\approx5.2988`$, $`C_3\approx16.7002`$ and $`C_4\approx36.3872`$ (exact relative-entropy formulas are in Theorem 1); $`k=1`$ needs one sample. Theorem 2 gives $`m_*(N,k)\sim N\log N/h_+(1/2)`$ for $`k=N-o(N)`$. Sampling is with replacement, distortion is $`1/2`$, and the results include success probability $`0.9`$. The uniform intermediate-sparsity target remains open.

See the [manuscript](../../references/colbrook-frames-2026-09-11/manuscripts/sampling_thresholds.pdf), [independent agent review](../../references/colbrook-frames-2026-09-11/verification/reviews/sampling-review.md), and [reproducible submission record](../../references/colbrook-frames-2026-09-11/README.md). Independent agent review is not external human peer review or formal proof-assistant certification. Original problem, ratings and historical audits are retained below.
<!-- /colbrook-frames -->

Let $`N=2^d`$ with $`d\ge1`$ and index rows and columns by $`\mathbb F_2^d`$. The normalized Walsh matrix is

```math
(H_N)_{a,b}=N^{-1/2}(-1)^{a\cdot b}.
```

For $`m\ge1`$, choose row indices $`a_1,\ldots,a_m`$ independently and uniformly with replacement and set $`\Phi=\sqrt{N/m}(H_N)_{(a_1,\ldots,a_m),:}`$. Let $`E_{m,N,k}`$ be the event that

```math
\tfrac12\|x\|_2^2\le\|\Phi x\|_2^2\le\tfrac32\|x\|_2^2
\quad\text{for every }x\in\mathbb R^N\text{ with }|\mathop{\mathrm{supp}}\nolimits x|\le k.
```

Define

```math
m_*(N,k)=\min\{m\in\mathbb N:m\ge1,\ \Pr(E_{m,N,k})\ge0.9\}.
```

**Problem.** Determine $`m_*(N,k)`$ up to universal multiplicative constants, uniformly for $`1\le k\le N`$, including all necessary logarithmic factors. The same sample must work for all sparse vectors. This is a quantitative restatement of the published sampling gap, not a separately numbered conjecture; the success probability and distortion fix a convention.

The Walsh transform is the Fourier transform on $`\mathbb F_2^d`$. Its subspace structure differs from the cyclic Fourier ensemble in FR-02, so their lower bounds cannot be interchanged.

## References

1. J. Błasiok, P. Lopatto, K. Luh, J. Marcinek, and S. Rao, *An improved lower bound for sparse reconstruction from subsampled Walsh matrices*, Discrete Analysis 2023:3, introduction and Theorem 3.1. [Paper](https://arxiv.org/abs/1903.12135).
2. I. Haviv and O. Regev, *The restricted isometry property of subsampled Fourier matrices*, Theorem 1.1 and its bounded-orthonormal-matrix scope. [Paper](https://arxiv.org/abs/1507.01768).

## Status check — 2026-09-10

The lower-bound paper uses independent Bernoulli row inclusion; the upper-bound literature also treats independent draws with replacement, the explicit convention here. Its $`\Omega(k\log k\log(N/k))`$ obstruction applies in a specified intermediate sparsity range, not as an all-parameter formula. The logarithmic gap discussed there remains unclosed in the targeted search for later Walsh RIP results. Endpoint regimes must also be accounted for; in particular $`m_*(N,1)=1`$.

**Audit update (2026-09-10):** Rechecked the Walsh lower-bound record and Haviv–Regev upper bound, and searched for a later matching rate. The intermediate-sparsity obstruction is not an all-parameter formula. Difficulty is aligned with the comparable Fourier gap in FR-02. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
