# Sources consulted and attribution

Access date: September 12, 2026. The public repository and papers were read on the web. No GitHub plugin was used, and no repository changes or submissions were made.

## Problem formulation

**Open Problems in Numerical Linear Algebra, RE-06 — Nonadaptive queries for finite-family matrix approximation.** The page gives the exact oracle model, instance-wise probability quantifiers, 0.99 target, unrestricted candidate processing, and allowed logarithmic overhead. Its own status audit is dated September 10, 2026.

- Problem page: https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/randomized-and-low-rank-approximation/RE-06
- Raw statement: https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/randomized-and-low-rank-approximation/RE-06/README.md

The archive proves an affirmative answer to that formulation. It does not claim that the repository has accepted or independently checked the result.

## Adaptive finite-family context

**Noah Amsel, Pratyush Avi, Tyler Chen, Feyza Duman Keles, Chinmay Hegde, Cameron Musco, Christopher Musco, and David Persson. Query Efficient Structured Matrix Learning.** Proceedings of the 39th Conference on Learning Theory, PMLR 336:158–194, 2026. The referenced arXiv revision is v2, dated August 21, 2026.

- HTML: https://arxiv.org/html/2507.19290v2
- Conference record: https://proceedings.mlr.press/v336/amsel26a.html

Theorem 1 supplies the adaptive finite-family context; Section 5 explicitly raises the nonadaptive question. The present proof does not invoke the paper's adaptive algorithm as a subroutine.

## Independent two-sided low-rank reconstruction

**Joel A. Tropp, Alp Yurtsever, Madeleine Udell, and Volkan Cevher. Practical Sketching Algorithms for Low-Rank Matrix Approximation.** SIAM Journal on Matrix Analysis and Applications 38(4):1454–1485, 2017.

- HTML: https://arxiv.org/html/1609.00048v2
- Abstract and publication metadata: https://arxiv.org/abs/1609.00048

The reconstruction Q (H^T Q)^dagger H^T C from independent left and right sketches is a standard algorithm from this work; it is not presented as an original algorithmic ingredient. The solution derives the error majorant and probability conversion it needs in full.

## Gaussian range-finder background

**Nathan Halko, Per-Gunnar Martinsson, and Joel A. Tropp. Finding Structure with Randomness: Probabilistic Algorithms for Constructing Approximate Matrix Decompositions.** SIAM Review 53(2):217–288, 2011.

- Abstract and publication metadata: https://arxiv.org/abs/0909.4061

This is background for the randomized range approximation argument. The deterministic range majorant and Gaussian inverse moment used in the solution are proved in the note.

## What the archive adds

The mathematical contribution presented here is the trimmed-residual lower-tail argument combined with independent, prequeried residual correction, explicit constant-probability accounting, and the complete one-batch construction satisfying the stated RE-06 bound with b = 0. The note does not claim historical priority for every individual inequality or a comprehensive novelty search, and it has not been independently refereed or formalized.
