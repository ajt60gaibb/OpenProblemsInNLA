# Proof audit and dependency map

This document identifies the hypotheses and logical transitions in the proposed
TR-08 proof. It is not a formal verification certificate or a report from an
independent reviewer. All references to sections below are to `solution.pdf`.

## Scope and quantifiers

The matrix has exactly `k/100` selected columns and exactly `s_k` nonzeros per
column. Signs are independent both of one another and of all supports. Selection
of the column set is independent of the original matrix. The proof concerns
only the least singular value; it does not prove a two-sided embedding theorem.

The required constant is existential after the sparsity sequence is fixed.
The sufficiency statement supplies a single `a(h) > 0` for every sequence with
`s_k^2 >= h log k` eventually. All auxiliary constants `R`, `L`, and `D` depend
only on this fixed `h`, not on `k`. The proof explicitly waits until the growing
`s_k` exceeds these constants. No finite-size performance guarantee is implied
at modest dimensions.

## Logical dependency map

| Step | What it supplies | Inputs |
|---|---|---|
| Section 1 | Exact reduction to independent selected columns | Independence of selection and matrix columns |
| Section 2, incidence estimate | Joint upper-tail estimate for counts on a fixed row set | Uniform supports, column independence |
| Section 2, overlap estimate | All column pair overlaps at most two | `s_k <= (log k)^2` |
| Section 3 | Small nonbacktracking spectral radius after a prescribed support-only pruning | Independent signs, inclusion-probability comparison, Dumitriu–Zhu Lemma 4.3 |
| Section 4 | Lower singular-value bound for a capped-row, nondegenerate-column bulk | Uniform nonzero magnitudes, nonbacktracking radius bound |
| Section 5, exceptional neighbors | Bounded interaction with exceptional columns | Conditional incidence tails, bounded pair overlaps, `s_k^2 >= h log k` |
| Section 5, occupancy cap | Most of each column survives a larger row-degree cap | Conditional incidence tails |
| Section 5, block restriction | Full matrix has a positive lower singular-value bound | Bulk, disjoint exceptional supports, bounded coupling |
| Section 6 | Cancellation tree with high probability below the scale | Reservoir occupancy lower tail, row negative correlation, local graph cleaning, independent tests |
| Section 7 | Exact criterion for arbitrary sequences | Sufficiency and a subsequence application of necessity |

## The key conditional probability step

To bound exceptional neighbors, fix a center and `R` leaf columns and expose only
these supports. Restrict to configurations in which their pairwise overlaps are
at most two. If the leaves are all exceptional, each contains at least
`floor(d/3)` high-occupancy rows unique among the exposed supports, once `d` is
large compared with `R`. The chosen row sets are disjoint.

Each chosen row has only one exposed incidence, so its high occupancy must be
supplied by unexposed independent columns. The incidence moment-generating
function applies conditionally. A union bound over possible choices of rows
costs at most `2^(R d)`, whereas the tail has order `exp(-c R d^2)`.

The resulting conditional bound is uniform over the exposed configurations.
It can therefore be multiplied by the probability that all leaf supports meet
the center. It is not obtained by asserting independence of exceptional-column
events or independence of row occupancies. The global overlap event is handled
by adding its failure probability, not by conditioning the unexposed columns
on that event.

## Why the nonbacktracking transfer is legitimate

The pruned mask is a function of supports only. Conditional on supports, every
edge sign remains independent and symmetric. In the path expansion of the
squared Frobenius norm of a power of the nonbacktracking matrix, terms with any
odd edge multiplicity vanish. Every surviving term is nonnegative.

For a surviving term, retaining all of its distinct edges after pruning has
probability no greater than retaining those edges before pruning. The latter
probability factors over columns and is bounded by the corresponding iid
Bernoulli probability, since `(d)_r/(k)_r <= (d/k)^r`. This establishes an
expectation inequality term by term. It does not assert pointwise spectral
monotonicity under signed edge deletion.

The comparison uses a fixed complete-bipartite edge index set. Padded absent
edges add only zero eigenvalues. The deterministic bulk argument then uses the
operator on actual retained edges, with the same nonzero spectrum.

In the published trace-moment estimate, take `gamma = 1/100`, `kappa = 1`,
`delta = 1/6`, `q = min(sqrt(d), k^(1/20))`, and the least odd integer
`ell >= 10 log k`. The entry bound can be loose. Thus all the allowed ranges
hold eventually whenever `d -> infinity`, including the dense regime. The
Markov bound is a constant times
`(log k)^4 k^(21/10) (2/5)^ell`, which tends to zero.

## The deterministic spectral argument

The equal-magnitude assumption is used exactly: on every retained edge,
`H_uv H_vu = 1/d`. Solving the two opposite-edge equations gives the stated
Ihara–Bass kernel criterion. At the imaginary parameter `lambda = i sqrt(t)`,
the Schur complement is real symmetric, although the full block matrix is
complex symmetric rather than Hermitian.

For `t >= 1/4`, the first diagonal block is positive definite. The Schur
complement is nonsingular because `sqrt(t)` exceeds the nonbacktracking
spectral radius. Its eigenvalues cannot cross zero, and it approaches the
identity as `t -> infinity`. It is therefore positive definite. This is what
justifies the lower bound; the complex full matrix is not treated as positive
semidefinite.

The bulk lemma is applied to the nonzero good-column submatrix, not to the
padded matrix with its zero exceptional columns. Empty column classes cause
no difficulty: the corresponding inequalities are vacuous.

## The exact block restriction is essential

The first row set excludes the entire neighborhood of every exceptional
column. This creates a genuinely zero upper-right block. The second row set
contains capped-occupancy rows touching exactly one exceptional column. Hence
the exceptional block has mutually disjoint column supports.

A good column has at most `L` entries in the second row set. Each row there has
at most `D d` entries. Consequently the coupling norm is at most `sqrt(D L)`.
The resulting block-triangular matrix is bounded below by
`1/(6 + 8 sqrt(D L))`. This restriction deletes rows only; the norm of the full
matrix output is at least the norm of its restricted output.

The proof does not assume that arbitrary entry deletion improves a least
singular value. It also does not simply concatenate two independently good
column blocks while ignoring cancellation between them.

## The necessity witness uses full column supports

Only the reservoir is exposed before testing possible root columns. Upper-tail
indicators of two reservoir row counts have nonpositive covariance, as proved
by conditioning on one row count; they are not assumed independent.

Rows on four-cycles are excluded only from the candidate root-row set. The
reservoir graph and all of its supports remain unchanged. All graph distances
are measured in that original graph. Candidate root rows have pairwise distance
greater than four, which prevents overlap between different branches; exclusion
of four-cycle rows prevents overlap within a branch.

Every nonzero of each chosen column is included in the cancellation calculation.
Unused columns may touch the witness rows, but have zero vector coefficient.
The signs of the witness coefficients are chosen after the matrix is realized,
which is permitted in the variational definition of the least singular value.
The exact squared quotient is `(d-1)/(d+w)`. There are linearly many conditionally
independent test columns, each successful with probability at least
`exp(-C_epsilon d^2)`.

## Boundary and sequence checks

The sufficiency proof covers every fixed `h > 0`, not just a sufficiently large
one. The necessity proof covers fixed `d`, growing subthreshold `d`, and arbitrary
subthreshold subsequences. If the normalized ratio has lower limit zero,
extracting such a subsequence rules out convergence of the success probability
to one on the whole sequence. No monotonicity or stochastic ordering in `d`
is assumed.

## What the accompanying tests establish

The exact finite checks verify the displayed algebra and small instances of the
support and trace-moment inequalities. Floating-point tests check selected
Ihara–Bass and block examples. The recorded test run passes. These tests do not
verify all paths at unbounded powers, justify the external moment theorem, or
prove that the high-probability events hold asymptotically. Those tasks belong
to the mathematical proof and its independent review.
