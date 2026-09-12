# IE-10 — Conditioning of a random Krylov compression of a cyclic shift

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11  

<!-- colbrook-round3 -->
## Independently reviewed resolution - 2026-09-11

Theorem 1 proves $`\mathbb E\kappa_V(H_k)\leq17n^2k`$ for the exact complex-sphere cyclic-shift model. Markov\'s inequality gives the uniform $`0.99`$ target with $`C=1700`$ and $`c=3`$. Sections 5 and 6-7 give two probability proofs; real starts and arbitrary nonnormal inputs are outside the result.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](../../references/colbrook-round3-2026-09-11/manuscripts/IE-10.pdf), [independent proof review](../../references/colbrook-round3-2026-09-11/verification/reviews/IE-10-review.md), and [submission record](../../references/colbrook-round3-2026-09-11/README.md). The supplied manuscripts and code disclose AI generation. Agent review is not external human peer review or formal certification; no novelty or priority claim is made.

The difficulty, importance and rating rationale below are historical assessments of the original open target.

<!-- /colbrook-round3 -->

**Rating rationale:** Challenging reflects a least-singular-value bound for a dependent random Krylov matrix; specialist impact concerns a structured compression mechanism in eigenvalue algorithms.

## Problem statement

Let $`C_n\in\mathbb C^{n\times n}`$ be the cyclic shift, $`C_ne_j=e_{j+1}`$ for $`j< n`$ and $`C_ne_n=e_1`$. Draw $`b`$ uniformly from the complex unit sphere. For $`2\leq k< n`$, let $`Q`$ have orthonormal columns spanning

```math
\mathcal K_k(C_n,b)=\mathop{\mathrm{span}}\nolimits\{b,C_nb,\ldots,C_n^{k-1}b\},
\qquad H=Q^*C_nQ.
```

This subspace has dimension $`k`$ almost surely. Define $`\kappa_V(H)=\inf_{H=VDV^{-1},\ D\text{ diagonal}}\|V\|_2\|V^{-1}\|_2`$, and set it to $`+\infty`$ if $`H`$ is not diagonalizable. Do universal constants $`C,c>0`$ exist such that, for every $`n\geq3`$ and $`2\leq k< n`$, with the same constants,

```math
\Pr\{\kappa_V(H)\leq Cn^c\}\geq0.99?
```

Changing the orthonormal basis of the same Krylov space does not affect this question. Randomness belongs to the starting vector; replacing $`Q`$ by an independently Haar-distributed subspace would change the model.

## Reference

Amsel et al., [*Linear Systems and Eigenvalue Problems*](https://arxiv.org/html/2602.05394v3#S3.SS3), Problem 3.5, which explicitly singles out the circulant shift. This entry fixes “high probability” to a uniform 0.99 success target.

## Earlier status check — 2026-09-08

Searches for `Krylov circulant shift condition 2026` and `random Krylov compression eigenvector condition number` found no solution. The deterministic starting vector $`e_1`$ gives a Jordan compression, so the unrandomized statement would be false; that exceptional example does not settle the probabilistic problem. The workshop report’s 20 August update reports [Peng’s obstruction](https://yangpliu.github.io/repository.html) for arbitrary real diagonalizable inputs with ill-conditioned eigenvectors and real Gaussian starts. It explicitly leaves the normal-input case open, which includes the cyclic shift here.

## Audit update — 2026-09-10

Rechecked [workshop version 3](https://arxiv.org/html/2602.05394v3), Problem 3.5 and its August update. The arbitrary-diagonalizable counterexample does not cover this normal cyclic shift. Random Krylov/circulant conditioning searches found no bound resolving the displayed structured case.
