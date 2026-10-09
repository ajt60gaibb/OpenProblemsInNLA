# FR-10 — Sharp sampling complexity for Walsh restricted isometries

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Solved  
**Last checked:** 2026-09-30

**Rating rationale:** Closing the uniform logarithmic sampling gap is a longstanding restricted-isometry barrier comparable in scale to the cyclic Fourier problem, with consequences for sparse recovery and fast sketches.


## Statement

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

## Resolution — 2026-09-30

**Affirmative resolution.** Theorem 1.1 of [*Walsh restricted isometries under sampling with replacement*](../../references/haidary-resolutions-2026-09-30/Walsh_RIP_with_replacement_revised.pdf) ([LaTeX source](../../references/haidary-resolutions-2026-09-30/Walsh_RIP_with_replacement_revised.tex)), working manuscript dated 30 September 2026, proves

```math
m_*(N,1)=1,\qquad
c\,k\log(2k)\log(2eN/k)\le m_*(N,k)
\le C\,k\log(2k)\log(2eN/k)\quad(2\le k\le N),
```

with universal constants (the manuscript gives $`c=1/2000`$). This settles the exact with-replacement model, distortion $`1/2`$, success probability $`0.9`$, and whole sparsity range in the original target. Sections 2–4 extend the entropic encoding and probability argument to indexed repeated row occurrences, including sample counts above $`N`$; Sections 5–6 give the affine-subspace lower bound and all-sparsity completion.

**Attribution.** The submitter describes this manuscript as a trivial extension of W. Burstein, A. Iosevich and B. Krause, *Restricted isometry of sampled Fourier and Hadamard matrices via entropic descent*, [arXiv:2609.22568v1](https://arxiv.org/abs/2609.22568v1). The improved logarithmic upper rate and entropic encoding input are credited to that work. The lower-bound subspace obstruction is credited to Błasiok–Lopatto–Luh–Marcinek–Rao. **No novelty or priority is claimed for this local manuscript.** The order estimate does not supersede Colbrook's sharper endpoint leading constants recorded below.

**Review.** The supplied [ChatGPT 6 Pro audit](https://chatgpt.com/share/6abd4125-5848-83eb-9598-f9b2d8822c71) reports no substantive gap in the repeated-occurrence extension, paired-sign argument, fixed-draw affine second moment, or all-sparsity completion. The revised source incorporates the audit's LaTeX repair and explicit citations to BIK Lemmas 4.1–4.2 and 6.1. This is an informal AI audit, not external human peer review or formal proof-assistant certification. See the [submission record](../../references/haidary-resolutions-2026-09-30/README.md). Historical ratings are retained, and the original target is retained above; the September 11 partial-status notice is superseded by this resolution.

<!-- colbrook-frames -->
## Reviewed submission - 2026-09-11

Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge.

Theorem 1 proves $`m_*(2^d,k)/d\to C_k`$ for $`k=2,3,4`$, with $`C_2\approx5.2988`$, $`C_3\approx16.7002`$ and $`C_4\approx36.3872`$ (exact relative-entropy formulas are in Theorem 1); $`k=1`$ needs one sample. Theorem 2 gives $`m_*(N,k)\sim N\log N/h_+(1/2)`$ for $`k=N-o(N)`$. Sampling is with replacement, distortion is $`1/2`$, and the results include success probability $`0.9`$. The uniform intermediate-sparsity target remains open.

See the [manuscript](../../references/colbrook-frames-2026-09-11/manuscripts/sampling_thresholds.pdf), [independent agent review](../../references/colbrook-frames-2026-09-11/verification/reviews/sampling-review.md), and [reproducible submission record](../../references/colbrook-frames-2026-09-11/README.md). Independent agent review is not external human peer review or formal proof-assistant certification. The original problem, ratings and historical audits are retained on this page.
<!-- /colbrook-frames -->

## References

1. J. Błasiok, P. Lopatto, K. Luh, J. Marcinek, and S. Rao, *An improved lower bound for sparse reconstruction from subsampled Walsh matrices*, Discrete Analysis 2023:3, introduction and Theorem 3.1. [Paper](https://arxiv.org/abs/1903.12135).
2. I. Haviv and O. Regev, *The restricted isometry property of subsampled Fourier matrices*, Theorem 1.1 and its bounded-orthonormal-matrix scope. [Paper](https://arxiv.org/abs/1507.01768).

## Status check — 2026-09-10

The lower-bound paper uses independent Bernoulli row inclusion; the upper-bound literature also treats independent draws with replacement, the explicit convention here. Its $`\Omega(k\log k\log(N/k))`$ obstruction applies in a specified intermediate sparsity range, not as an all-parameter formula. The logarithmic gap discussed there remains unclosed in the targeted search for later Walsh RIP results. Endpoint regimes must also be accounted for; in particular $`m_*(N,1)=1`$.

**Audit update (2026-09-10):** Rechecked the Walsh lower-bound record and Haviv–Regev upper bound, and searched for a later matching rate. The intermediate-sparsity obstruction is not an all-parameter formula. Difficulty is aligned with the comparable Fourier gap in FR-02. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
