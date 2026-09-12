# PR125 independent mathematical and source review

**PASS at `96c83a5e5c4be73194f47d01e68a0a8f2a062e87`. No mathematical blocker found.** Both are affirmative, literature-dependent resolutions. Reviewed 2026-09-11, read-only; this report is independent of the submitted AI review.

Read both complete application notes (SP-11: 60 lines; SP-12: 107 lines), both canonical targets, the submission attribution/scope record, and Hall's essential proof through Theorem 3.20. The original canonical `## Problem statement` sections are byte-identical to the published `origin/main` versions. Full file and section hashes are in `PR125-review-evidence.json`.

## Hall's external input

Checked the pinned [primary preprint](https://arxiv.org/pdf/2601.01211v1), its [HTML](https://arxiv.org/html/2601.01211v1), and [current record](https://arxiv.org/abs/2601.01211). Only v1 is listed, submitted 3 January 2026; no journal acceptance or withdrawal is indicated. Theorem 3.20 and Corollary 3.22 give the required all-graph PSD/SAP existence bound; Corollary 3.24 explicitly gives SP-11's ordinary Delta conclusion.

The essential proof checks: alternating-tensor contraction produces polynomial orthogonal representations; greedy ordering supplies the child-index bounds; Lemma 5.14 prevents cancellation; real generic parameter choices make all required Gram entries nonzero simultaneously. Nonzero representation vectors force each preceding-nonneighbor set independent. The Gram matrix is PSD and upper-zero generic; Theorem 3.12's last-nonzero-column argument gives SAP. Its nullity is at least the final vertex degree, hence minimum degree.

Two source issues are nonessential: Proposition 5.12 needs i<j, which its used Corollary 5.13 includes; the weak-success parenthetical cannot follow from dimension counting alone, but the later diagonal-polynomial nonvanishing proves it. The abstract's “definite” must read semidefinite, as the definitions and construction specify. Unused extensions and the NP-hardness appendix are outside this review.

## Independent check of the delicate repeated-variable step

I reconstructed the leading-term optimization, rather than accepting the submitted report. Process vertex classes in increasing vertex order. Each ordinary occurrence of the current class has its lower incident indices fixed to the prefix 1,...,k; each preceding sibling's index is fixed too. The smallest permitted upper index is its sibling position, including the augmented list at the exceptional top pair. The greedy inequalities make that index exceed k. Occurrences of the same class are never siblings, so their choices do not compete for a conduit at one parent.

For a fixed class, all independent variables therefore have the same fixed lower prefix and differ only in the upper index. Assigning each occurrence its individual least permitted index uniquely maximizes their joint monomial, even though occurrences share variables: any different assignment must increase an index; at the first affected variable it loses multiplicity and cannot compensate by decreasing another occurrence below its permitted minimum. The prescribed pattern extends through later classes, so it is globally feasible. Equal top labels have identical lower patterns and the shared upper index k+1. This supplies the uniqueness needed to rule out cancellation without assuming distinct variables for repeated nodes.

A fresh standard-library symbolic implementation expands the actual contraction polynomials and separately counts signed coefficients and unsimplified term occurrences. Across 31 greedily ordered labeled graphs (all orders through three vertices, and four-vertex orders with at most two preceding nonneighbors), 198 diagonal/edge leading monomials each occur exactly once with coefficient ±1; every nonedge polynomial is zero. It also reproduces the four-vertex non-greedy cancellation example. These are finite stress checks, not a replacement for the all-graph argument. Code/output: `PR125-leading-monomial-check.py` and `.json`.

## Application SP-11

`eigenvalues-and-inverse-problems/SP-11/solution.md`, external theorem and deduction sections: Hall's real PSD exact-pattern SAP witness remains admissible after forgetting PSD and SAP. Rank-nullity gives precisely mr(G) <= n-delta(G). Diagonals remain unrestricted, edge weights are not prescribed, and no connectedness condition is introduced. The delta=0 endpoint is trivial. PASS.

## Application SP-12

`eigenvalues-and-inverse-problems/SP-12/solution.md:42`–82: the fixed-rank PSD manifold tangent/normal calculation is correct. The normal space is exactly symmetric X with AX=0. Failure of surjectivity of the nonedge-coordinate map would supply a nonzero normal matrix supported on off-diagonal nonedges, contradicting SAP. A local submersion section therefore supplies D_epsilon converging to A with the specified entries.

The Schur complement construction is PSD, has rank r+1 and preserves nullity. Old nonedges cancel exactly, old edges stay nonzero by continuity, and new edges have exactly the prescribed support. SAP is correctly checked on the fixed vector space Z_G, including at B_0 even though B_0 itself need not have all new edges: the first row kills the new row/column of X, and SAP of A kills the old block. Injectivity is open, so the perturbed exact-pattern matrix has SAP.

The rank-zero case causes no exception. A=0 with exact pattern has an edgeless graph, and SAP then permits at most one vertex; thus the nonedge-coordinate target is zero-dimensional and the claimed surjectivity is valid. No connectedness is used anywhere.

Lines 87–95: a minimal induced subgraph with chromatic number k has minimum degree at least k-1 by the usual extension-of-coloring contradiction. Combining induced-subgraph monotonicity with Hall gives precisely nu(G)>=chi(G)-1. The k=1 case is immediate. No minor-contraction theorem, Hadwiger assumption, or stronger invariant is silently substituted. PASS.

## Attribution and review limits

Hall is credited for the substantive theorem. George Stepaniants is credited for the explanatory application notes, with substantial AI assistance disclosed. The notes call the source a preprint and do not claim human peer review, formal certification, or new discovery. Their Solved status is supported by this independent essential-proof/application audit, with the external preprint dependence explicit.

No repository files were changed and no submitted network/packaging scripts were executed. PDF QA, integration and required CI are assigned to the integrating agent.
