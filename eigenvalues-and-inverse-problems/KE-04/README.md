# KE-04 — Strict interlacing across block Lanczos iterations

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved  
**Last checked:** 2026-09-11  

**Rating rationale:** Challenging reflects a stronger strict interlacing law than general compression interlacing supplies; community impact is spectral information across block Krylov iterations.

## Resolution — 2026-09-11

**Affirmative resolution by Matthew J. Colbrook** (Department of Applied Mathematics and Theoretical Physics, University of Cambridge). See the [complete manuscript](solution.md), **Theorem KE-04, sections 1–3** ([PDF](solution.pdf) · [LaTeX](solution.tex)), prepared 11 September 2026.

Strict interval occupancy holds for every allowed pair of block Lanczos iterations and every indicated index, in exact arithmetic before the first loss of full block dimension. The quadratic-polynomial argument includes multiplicities and excludes coincident interval endpoints in the stated range.

The original proof draft was generated in a ChatGPT conversation. A separate Codex agent independently verified the full proof and its match to the exact target on 11 September 2026: [detailed PASS review](../../references/colbrook-2026-09-11/verification/reviews/KE-04-review.md). The review records a hash of the unchanged proof text. This is independent agent verification, not external human peer review or formal certification. [The submission history and diagnostic record](../../references/colbrook-2026-09-11/README.md) preserve the initial solution claim. The ratings above are historical, and the earlier literature checks below are retained.

## Original problem statement

Let $`A\in\mathbb R^{n\times n}`$ be symmetric and $`V\in\mathbb R^{n\times p}`$ have full column rank. Write

```math
\mathcal K_j=\mathop{\mathrm{range}}\nolimits[V,AV,\ldots,A^{j-1}V],
```

and let $`s`$ be the largest integer with $`\dim\mathcal K_s=sp`$. For $`1\le j\le s`$, choose an orthonormal basis $`Q_j`$ of $`\mathcal K_j`$ and order the eigenvalues of $`T_j=Q_j^TAQ_j`$ as
$`\theta_1^{(j)}\le\cdots\le\theta_{jp}^{(j)}`$, with multiplicity.

For every $`1\le k<j\le s`$ and $`1\le i\le(k-1)p`$, must the open interval

```math
(\theta_i^{(k)},\theta_{i+p}^{(k)})
```

contain an eigenvalue of $`T_j`$? The statement concerns exact arithmetic before the first loss of full block dimension. Although Lanczos supplies compatible block tridiagonal representations, the spectra do not depend on the chosen bases.

This would extend a scalar Lanczos property used to interpret later Ritz values and distinguish genuine eigenvalue approximation from clusters created by finite precision.

## References

 D. Šimonová and P. Tichý, *On finite precision block Lanczos computations*, arXiv:2507.16484v1 (22 July 2025), §2.1, unnumbered conjecture and final discussion ([primary manuscript](https://arxiv.org/html/2507.16484v1)). J. Liesen and Z. Strakoš, *Krylov Subspace Methods: Principles and Analysis*, Oxford 2013, the scalar Lanczos/orthogonal-polynomial background cited by the source ([publisher](https://doi.org/10.1093/acprof:oso/9780199655410.001.0001)).

## Status check — 2026-09-08

 The arXiv abstract/history and full §2.1 were inspected; v1 remains the only listed version. Searches “block Lanczos interlacing conjecture”, “Šimonová Tichý interlacing”, and 2026 proof/counterexample queries found no resolution. Standard weak Cauchy interlacing is not the asserted strict interval-occupancy result.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

## Audit update — 2026-09-10

Rechecked the explicit conjecture and concluding discussion in the [2025 block-Lanczos manuscript](https://arxiv.org/html/2507.16484v1). Its block-width index ranges agree with this entry. Searches for later strict block-Lanczos interlacing proofs found no resolution; ordinary Cauchy interlacing is weaker than the displayed claim.
