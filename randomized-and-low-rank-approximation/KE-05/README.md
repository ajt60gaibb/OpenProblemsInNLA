# KE-05 — Spectral-gap-independent constants for randomized block polynomial interpolation

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** explicit conjecture in a May 2026 primary revision  
**Last checked:** 2026-09-08

Fix integers $b\ge1$, $d\ge2$. Let $\Lambda_1,\ldots,\Lambda_d\in\mathbb R^{b\times b}$ be diagonal with pairwise disjoint spectra. Draw all entries of $\Omega_1,\ldots,\Omega_d\in\mathbb R^{b\times b}$ independently from $N(0,1)$ and put $B_i=\Omega_i^{-1}\Lambda_i\Omega_i$. Let $a$ and $c$ be the smallest and largest diagonal entries in the entire family.

For each $k\in\{1,\ldots,d\}$, reorder the triples $(B_i,\Lambda_i,\Omega_i)$ into the order $(k,1,\ldots,k-1,k+1,\ldots,d)$ and use superscript $(k)$ for that ordering. In descending order $i=d,d-1,\ldots,1$, compute
$$
S_{i,i}^{(k)}=I_b,\qquad
S_{i,j}^{(k)}=B_i^{(k)}S_{i,j-1}^{(k)}-S_{i,j-1}^{(k)}\widehat B_j^{(k)}
\quad(j=i+1,\ldots,d),
$$
$$
\widehat\Omega_i^{(k)}=\Omega_i^{(k)}S_{i,d}^{(k)},\qquad
\widehat B_i^{(k)}=(\widehat\Omega_i^{(k)})^{-1}\Lambda_i^{(k)}\widehat\Omega_i^{(k)}.
$$
All norms below are spectral norms. Define
$$
\chi_{\rm mono}^{(k)}=
\max_{2\le i\le d}\left\{
1,\frac{\|aI-\widehat B_i^{(k)}\|_2}{\|aI-\Lambda_i^{(k)}\|_2},
\frac{\|cI-\widehat B_i^{(k)}\|_2}{\|cI-\Lambda_i^{(k)}\|_2}\right\},
$$
$$
\chi_{\rm coef}^{(k)}=
\|(S_{1,d}^{(k)})^{-1}\|_2^{1/(d-1)}
\min_{\substack{2\le i\le d\ ,\ \lambda\in\sigma(\Lambda_1^{(k)})\\
\eta\in\sigma(\Lambda_i^{(k)})}}|\lambda-\eta|,
\qquad
\chi_{\rm mono}=\max_k\chi_{\rm mono}^{(k)},\quad
\chi_{\rm coef}=\max_k\chi_{\rm coef}^{(k)}.
$$
The inverses exist almost surely, as shown in the source. If an endpoint ratio is $0/0$, set it to 1; its matrix is necessarily a scalar matrix and the surrounding maximum already includes1.

Is the family of random variables $\chi_{\rm mono}\chi_{\rm coef}$ uniformly bounded in probability over all admissible diagonal data? Precisely, for each $0<\delta<1$, does there exist a finite $C(b,d,\delta)$ such that, for every fixed admissible $(\Lambda_1,\ldots,\Lambda_d)$,
$$
\Pr\{\chi_{\rm mono}\chi_{\rm coef}\le C(b,d,\delta)\}\ge1-\delta?
$$
The constant must be independent of the eigenvalues and all gaps within and between their blocks. Probability is taken separately for each fixed input, not for one draw required to work simultaneously for every spectrum. This quantifies the source's “with high probability” statement with its explicitly allowed failure-probability dependence.

These constants control matrix-polynomial interpolation in the convergence analysis of randomized small-block Lanczos. The bound would explain robustness to clusters much larger than the starting block. The scalar-block case is already bounded deterministically; noncommutativity is the unresolved obstacle.

## References

 N. Shao, *A structural bound for cluster robustness of randomized small-block Lanczos*, arXiv:2507.10144v2,30 May 2026, Theorem 1, equation(12), and Conjecture 1 in §3.2 ([primary full text](https://arxiv.org/html/2507.10144v2)). T. Chen et al., *Does block size matter in randomized block Krylov low-rank approximation?*, arXiv:2508.06486, §§4,6 ([primary paper](https://arxiv.org/abs/2508.06486)), is related: its conjecture changes spectral-gap dependence in output bounds, whereas this question bounds the intermediate random interpolation constants themselves.

## Status check — 2026-09-08

 Latest arXiv abstract/history and May 2026 v2 inspected. The revision explicitly retains Conjecture 1, including independence of gaps within and between blocks. Searches for author/title with “proof”, “conjecture”, “cluster robustness”, and 2026 found no resolution. Generic nonsingularity of the recurrence does not give the claimed uniform probabilistic bound.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
