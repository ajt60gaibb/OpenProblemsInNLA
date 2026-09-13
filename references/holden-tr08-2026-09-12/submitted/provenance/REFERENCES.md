# Sources and provenance

Access date: 12 September 2026. The primary sources were read from their public
websites. No external paper is reproduced in this archive.

## Problem statement

Open Problems in Numerical Linear Algebra, **TR-08: Sharp sparsity threshold for
injectivity of a random sparse rectangular matrix**.

- https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/randomized-and-low-rank-approximation/TR-08
- https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/randomized-and-low-rank-approximation/TR-08/README.md

The statement examined asks for necessary and sufficient conditions for the
existence of some fixed positive lower singular-value bound. Its clarification
of 12 September 2026 explicitly distinguishes this target from determining only
a critical logarithmic exponent. The displayed status at access was Open; this
archive is a proposed solution, not a claim that the repository has accepted or
changed its status.

## Source of the problem and obstruction idea

Han Huang, Mark Rudelson, and Konstantin Tikhomirov,
**Well-invertible column subsets of sparse matrices are rare**,
arXiv:2607.05384v2 (2026).

- https://arxiv.org/html/2607.05384v2
- https://arxiv.org/abs/2607.05384v2

Relevant locations: Section 1.3.1 (the obstruction pattern), and Section 7,
Problem 7.2 with its following paragraph. The cancellation-tree idea is credited
to this source. The present manuscript gives its own reservoir construction and
probability estimates for the varying-sparsity fixed-column model; it does not
claim that the source establishes the proposed square-root-logarithmic criterion.

## Sole non-elementary external proof input

Ioana Dumitriu and Yizhe Zhu,
**Extreme singular values of inhomogeneous sparse random rectangular matrices**,
*Bernoulli* 30(4), 2904–2931 (2024), DOI 10.3150/23-BEJ1699;
arXiv:2209.12271v4, revised 12 December 2024.

- https://arxiv.org/abs/2209.12271v4
- https://arxiv.org/html/2209.12271v4
- https://arxiv.org/pdf/2209.12271v4

Exact input: **Lemma 4.3**, equations (4.1)–(4.2), under Assumption 3 and the
centered-independent-entry setting of Section 4. In the version examined, the
lemma appears on printed PDF page 12. Section 5 explains the complete-bipartite
path expansion. The manuscript specializes the parameters and proves a
termwise comparison to transfer the estimate to fixed-size supports and to a
prescribed support-dependent pruning.

The deterministic imaginary-parameter argument is in the same mathematical
framework as this source's Section 3. The particular equal-magnitude lemma used
here is derived in full in Section 4 of `solution.pdf`; the general
independent-entry least-singular-value theorem is not applied to dependent
fixed-column supports.

## Contribution and review status

The proposed threshold theorem and its sufficiency/necessity arguments are the
research work supplied in this archive. They are not attributed as established
results to the cited sources. The proof has been checked during its preparation
and has supplementary executable sanity checks, but has not been independently
refereed, accepted by the problem maintainers, or certified in a proof assistant.
