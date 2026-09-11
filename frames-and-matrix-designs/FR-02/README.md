# FR-02 — Sharp sample complexity for restricted isometries from the cyclic Fourier matrix

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** The sharp uniform Fourier sampling rate is a longstanding barrier at the interface of harmonic analysis, sparse recovery and fast numerical sketches.


<!-- colbrook-frames -->
## Reviewed submission - 2026-09-11

Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge.

Theorem 2 establishes $m_*(N,s)\sim N\log N/h_+(1/3)$ for $s=N-o(N)$, where $h_+(t)=(1+t)\log(1+t)-t$, in the stated cyclic Fourier model with replacement and complex vectors. It includes $s=N$. This does not give the uniform rate over all sparsities; the Walsh low-sparsity constants do not transfer to arbitrary cyclic Fourier matrices.

See the [manuscript](../../references/colbrook-frames-2026-09-11/manuscripts/sampling_thresholds.pdf), [independent agent review](../../references/colbrook-frames-2026-09-11/verification/reviews/sampling-review.md), and [reproducible submission record](../../references/colbrook-frames-2026-09-11/README.md). Independent agent review is not external human peer review or formal proof-assistant certification. Original problem, ratings and historical audits are retained below.
<!-- /colbrook-frames -->

Let $F_N\in\mathbb C^{N\times N}$ be the unitary cyclic discrete Fourier matrix,
$$
(F_N)_{j\ell}=N^{-1/2}\exp(-2\pi\mathrm i j\ell/N),\quad0\leq j,\ell<N.
$$
Choose $r_1,\ldots,r_m$ independently and uniformly from $\{0,\ldots,N-1\}$, allowing repetitions, and form $A=\sqrt{N/m}(F_N)_{(r_1,\ldots,r_m),:}$. Put
$$
\delta_s(A)=\sup_{\substack{x\in\mathbb C^N\setminus\{0\}\\|\operatorname{supp}(x)|\leq s}}
\left|\frac{\|Ax\|_2^2}{\|x\|_2^2}-1\right|,
\qquad
m_*(N,s)=\min\{m\geq1:\Pr[\delta_s(A)\leq1/3]\geq2/3\}.
$$
Determine the order of $m_*(N,s)$, within absolute multiplicative constants, uniformly for integers $N\geq2$ and $2\leq s\leq N$. In particular, identify the logarithmic factors that are necessary rather than artifacts of current upper bounds.

The problem fixes the group to cyclic Fourier, the sampling to independent rows with replacement, and the success and distortion thresholds to constants. Results for Walsh–Hadamard matrices do not automatically give the same sharp answer for every cyclic $N$. This distinction matters because lower bounds can depend on subgroup structure.

Fast multiplication by Fourier sketches is valuable in large least-squares and sparse recovery computations. The source asks how many Fourier rows suffice for a fixed restricted-isometry tolerance. Haviv–Regev's upper bound is $O(s\log^2(s)\log N)$ at fixed tolerance; known lower bounds leave a logarithmic gap in general.

## References

1. A. S. Bandeira, *Ten Lectures and Forty-Two Open Problems in the Mathematics of Data Science*, Open Problem 6.1, including its explicit sampling-with-replacement Fourier model. [Author's notes](https://people.math.ethz.ch/~abandeira/TenLecturesFortyTwoProblems.pdf).
2. I. Haviv and O. Regev, *The Restricted Isometry Property of Subsampled Fourier Matrices*, SODA 2016; Geometric and Functional Analysis 27 (2017), pp. 119–142. Main restricted-isometry theorem. [Paper](https://arxiv.org/abs/1507.01768).
3. A. S. Bandeira, M. E. Lewis, and D. G. Mixon, *Discrete uncertainty principles and sparse signal processing*, Journal of Fourier Analysis and Applications 24 (2018), pp. 935–956. Theorem 16 gives a Fourier sampling lower bound under stated divisibility hypotheses. [Paper](https://arxiv.org/abs/1504.01014).

## Status check — 2026-09-10

Searched “subsampled Fourier RIP sharp logarithmic 2025 2026”, “cyclic Fourier RIP lower bound”, and the exact upper-bound title; checked current arXiv records. No uniform sharp-order resolution was found. Bounds for partial circulant Gaussian operators and Boolean Walsh transforms concern different random matrices.

**Audit update (2026-09-10):** Rechecked Haviv–Regev’s current record and searched for sharp cyclic Fourier RIP rates. The known upper bound leaves a logarithmic gap; Boolean Walsh lower bounds do not supply a uniform cyclic-group answer. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
