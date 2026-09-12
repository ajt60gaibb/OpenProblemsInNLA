# SP-07 — The sharp spectral-matching constant for normal matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-10  

**Rating rationale:** Extreme reflects a longstanding sharp-constant problem beyond the false constant-one conjecture; community impact is eigenvalue matching and perturbation theory for normal matrices.

## Problem statement

For normal matrices $`A,B\in\mathbb C^{n\times n}`$, list their eigenvalues
$`\alpha_1,\ldots,\alpha_n`$ and $`\beta_1,\ldots,\beta_n`$ with algebraic
multiplicity. Define the bottleneck matching distance

```math
d_\infty(A,B)=\min_{\pi\in S_n}\max_{1\le j\le n}
|\alpha_j-\beta_{\pi(j)}|,
```

where $`S_n`$ is the permutation group. Determine the exact value of

```math
C_{\rm normal}=\sup_{n\ge2}\ \sup_{\substack{A,B\in\mathbb C^{n\times n}\ \mathrm{normal}\\ A\ne B}}
\frac{d_\infty(A,B)}{\|A-B\|_2}.
```

Here normal means $`AA^*=A^*A`$, and $`\|\cdot\|_2`$ is the spectral norm.
The target is a single sharp constant valid in every dimension. Equivalently,
find the smallest $`C`$ for which $`d_\infty(A,B)\le C\|A-B\|_2`$ for all such
pairs, with matching sharpness evidence. The conjectured value $`C=1`$ has
already been refuted; it is not the question being posed.

## Why it matters

This is a sharp conditioning question for the complete spectrum of a normal
matrix. Matching counts repeated eigenvalues, so a Hausdorff-distance estimate
that ignores multiplicity does not answer it.

## References

R. Bhatia, [*Perturbation Bounds for Matrix Eigenvalues*](https://epubs.siam.org/doi/10.1137/1.9780898719079.ch9), SIAM, 2007, Chapter IX, pp. 154–155; the question is restated as Problem 27 in X. Zhan, [*Open problems in matrix theory*](https://math.ecnu.edu.cn/~zhan/papers/ZhanICCM.pdf), §21, pp. 12–13. P. Šemrl, [*Geometrical techniques in linear algebra*](https://indico.ictp.it/event/a08167/session/73/contribution/52/material/0/0.pdf), ICTP lecture notes, 2009, p. 10, Theorem 5 and the following open question. J. A. Holbrook, [*Spectral variation of normal matrices*](https://doi.org/10.1016/0024-3795(92)90047-E), LAA 174 (1992), 131–144.

## Earlier status check — 2026-09-08

The cited sources distinguish the unresolved sharp constant from Holbrook's
counterexample to one. They give $`1<C_{\rm normal}<3`$. A. Parusiński and A. Rainer,
[*Eigenvalue stability of Hermitian and normal matrices*](https://arxiv.org/abs/2603.23056),
v1 (2026), Proposition 3.4, still states the classical universal bound with
$`1<C<3`$; it does not determine the sharp constant. Searches for
`sharp spectral variation constant normal matrices`, `spectral variation best
possible constant`, and 2025/2026 follow-ups found no exact value. The explicit
open-question sources are historical; the recent bound is context, not an
explicit reaffirmation of openness. This is a bounded literature check.

## Audit update — 2026-09-10

The [2026 spectral perturbation manuscript](https://arxiv.org/pdf/2603.23056), Proposition 3.4, still uses a universal constant strictly between 1 and 3 rather than determining the optimum. Sharp-normal-spectral-matching searches found no exact value. This supports the retained open verdict alongside the historical lower-bound examples cited above; the old constant-one statement is already false and is not the target here.
