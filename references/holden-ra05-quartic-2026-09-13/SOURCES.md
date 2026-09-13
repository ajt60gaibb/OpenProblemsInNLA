# Primary sources and their exact roles

The canonical target and the imports below were read directly from the public
websites during this September 2026 continuation. No GitHub plugin was used.
The manuscript includes its own bibliography. No external paper is represented
as proving the new second upper branch.

## Canonical target

OpenProblemsInNLA, RA-05: “Sharp joint rank and accuracy dependence for strong
ell_p subspace coresets.” The entry retains arbitrary input rank, nonnegative
weights on original rows, every query of dimension at most k, and an
up-to-logarithms size/existence target with no extra running-time requirement.
At the check in this continuation its status line read Open.

https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/randomized-and-low-rank-approximation/RA-05/README.md

## Preliminary upper bound

H. Lin, V. Mirrokni, and D. P. Woodruff, *Nearly Optimal Strong Coresets for
ell_p Subspace Approximation*, arXiv:2608.26047v2, 27 August 2026.
**Theorem 1.2** is used at p = 4, with a fixed positive success probability.
It gives the k^2 epsilon^(-2) log^9 branch and preliminary original-row reduction.
Section 1.4 distinguishes the remaining joint-dependence problem.

https://arxiv.org/html/2608.26047v2

## Partial coloring

T. Rothvoss, *Constructive Discrepancy Minimization for Convex Sets*,
arXiv:1404.0339v4, 12 April 2016; SIAM Journal on Computing 46(1), 224–234 (2017).
**Lemma 9**, PDF page 8 (zero-based page 7), gives a partial coloring in a large
subspace from an arbitrary center in the open cube. The page image was checked
to disambiguate the extracted fraction: delta = (3/2) xi log_2(1/xi), not 32 xi
and not a squared logarithm. Fixing an allowed xi gives the absolute constants
used in the manuscript.

https://arxiv.org/pdf/1404.0339

## Matrix Gaussian series

J. A. Tropp, *User-Friendly Tail Bounds for Sums of Random Matrices*,
Foundations of Computational Mathematics 12(4), 389–434 (2012),
arXiv:1004.4389. **Theorem 1.5**, the rectangular Gaussian/Rademacher series
bound, controls the maximum of the left and right variance operator norms.
The coefficient-projection and anisotropic-whitening consequences needed here
are proved in this manuscript, rather than treated as separate imports.

https://arxiv.org/html/1004.4389v7

## Restricted invertibility, lower bound only

A. W. Marcus, D. A. Spielman, and N. Srivastava,
*Interlacing Families III: Sharper Restricted Invertibility Estimates*,
arXiv:1712.07766. **Theorem 1.1** states the Spielman–Srivastava stable-rank
restricted-invertibility theorem. It is applied after spectral truncation in
the cubic-core lower construction, with the number of selected columns at most
one quarter of the truncated stable rank.

https://arxiv.org/html/1712.07766

## Related exposition, not a new premise

Y. Li, *Near-Optimal Embeddings of Constant-Dimensional Subspaces of L_p into
ell_p^N*, arXiv:2607.11747v4, 27 July 2026. Theorem 4.4 restates the Rothvoss
lemma in an absolute-constant form. The proof here cites and checks the original
Rothvoss lemma; it does not import an all-rank subspace-coreset result from Li.

https://arxiv.org/html/2607.11747v4

## Repository status rules

OpenProblemsInNLA, RESOLVED.md, opening status and evidence-level definitions.
A surviving part of the original mathematical target remains PARTIAL, even if
a restricted result has stronger verification. Independent audit and formal
verification are distinct from an author-side proof check.

https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/RESOLVED.md

## Prior conversation artifact

`prior_work/RA05_rank_classification_package.zip` is the exact unchanged ZIP
provided earlier in this conversation, not an external peer-reviewed source.
Its own nested predecessors remain intact. The present manuscript reproves the
lower results it needs; it does not turn an earlier author-side claim into an
independent external citation.
