# Sources and provenance

Access date: September 12, 2026. GitHub content was read through its public website/raw webpage, not through a GitHub plugin. The library was used only to retrieve the user's earlier manuscript. No external write was performed.

## Canonical target

Alex Townsend, *Open Problems in Numerical Linear Algebra*, RA-05, “Sharp joint rank and accuracy dependence for strong l_p subspace coresets.” The canonical page states the original-row, nonnegative-weight, all-subspaces-of-dimension-at-most-k model and asks both for an optimal joint classification and for the displayed additive upper bound. The page displayed “Open” and a last-check date of September 10, 2026 when read for this work.

Canonical location:
`https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/randomized-and-low-rank-approximation/RA-05`

Raw statement read:
`https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/randomized-and-low-rank-approximation/RA-05/README.md`

Repository status definitions:
`https://github.com/ajt60gaibb/OpenProblemsInNLA`

The site is mutable; no immutable repository commit is claimed by this package.

## Upper-bound comparison

Honghao Lin, Vahab Mirrokni, David P. Woodruff, *Nearly Optimal Strong Coresets for l_p Subspace Approximation*, arXiv:2608.26047v2, August 27, 2026.

`https://arxiv.org/html/2608.26047v2`

Theorem 1.2 supplies the stated row-subset upper bound with size
`C_p k^(p/2) epsilon^(-2) log(C_p k/(epsilon delta))^(p+5)`.
Section 1.4 identifies the joint-dependence gap. The manuscript uses the theorem only to state a matching-order consequence, not as a premise in its lower-bound proof.

## Imported structural theorem

Adam W. Marcus, Daniel A. Spielman, Nikhil Srivastava, *Interlacing Families III: Sharper Restricted Invertibility Estimates*, arXiv:1712.07766v1, December 2017.

`https://arxiv.org/abs/1712.07766`
`https://arxiv.org/html/1712.07766`

Theorem 1.1 states the stable-rank restricted-invertibility theorem attributed there to Spielman–Srivastava. The exact theorem was checked in the HTML and on PDF page 2 (zero-based page 1). The required formulation has no unit-column assumption. The package imports the theorem, rather than claiming to re-prove or numerically verify it.

## Quartic construction background

P. Oscar Boykin, Meera Sitharam, Mohamad Tarifi, Pawel Wocjan, *Real Mutually Unbiased Bases*, arXiv:quant-ph/0502024, 2005.

`https://arxiv.org/abs/quant-ph/0502024`

The new manuscript gives its own finite-field construction and verification of the identities it uses. The reference identifies the classical background object, not priority for this package's coreset lower bound.

## Other reference in the canonical entry

David P. Woodruff, Taisuke Yasuda, *Root Ridge Leverage Score Sampling for l_p Subspace Approximation*, arXiv:2407.03262, FOCS 2025.

`https://arxiv.org/abs/2407.03262`

This is background. No unquoted result from it is a premise in the new lower-bound proof.

## User's earlier manuscript

`prior_work/RA05_counterexample.pdf` is the user's earlier same-day ChatGPT manuscript, *Counterexamples to the proposed joint coreset bound at p=4*. It was retrieved from the user's Library and materialized unchanged. It is unpublished prior-session work, not an external research publication.

The earlier manuscript proves quartic counterexamples and an accuracy-range lower bound, but explicitly does not classify all exponents or accuracies. The new manuscript retains a self-contained explicit quartic argument and develops a separate all-real-p core and finite-difference proof. No unproved assertion in the earlier file is used as a premise.

## Search limits

Targeted searches for later strong-coreset and joint-dependence results did not supply a competing resolution during this session. This is a bounded literature check, not a priority claim or proof that no related argument exists elsewhere.
