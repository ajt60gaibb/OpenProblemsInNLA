# Review checklist

## Mathematical self-checks completed

The sampling rules match standard RPCholesky and entry-squared RPLU. Exactly `r` pivots are compared with a best rank-`r` approximation. The RPLU denominator and numerator both use **squared** Frobenius error.

The `2 x 2` RPLU example has all four pivots enumerated with exact probabilities summing to one. The expected error is `18/5`, not a Monte Carlo approximation.

For the all-rank family, the review checks cover positive definiteness, entrywise positivity, nonzero Cauchy prefix minors, the inverse prefix-minor bound, the strict scale inequality `n^2 > s(s+1)`, relative residual asymptotics even for diverging interpolation vectors, the scale of the smallest eigenvalue, exact history cancellation, and the `2^r`/`4^r` history counts. Rank is fixed before the parameter limit; only finite sums are interchanged with that limit.

For LU, no independence of row and column histories is assumed. The proof uses a factorization of limiting indicators. It also does not substitute the singular matrix at `t=0` into the algorithm: doing so would lose rare-pivot contributions.

The correlation-matrix extension uses an isometric row replication and exact aggregation of pivot probabilities. The positive-definite perturbation is justified by a lower-semicontinuity argument over positive-probability histories. It does not incorrectly assume full continuity of LU expectations at zero entries.

The ten-test regression suite passes using exact rational arithmetic. It regenerates, rather than merely reads, the saved rank-eight certificate. Small-dimensional expected errors are independently computed by actual rank-one pivot updates. The replica identity is checked by another exact enumeration.

The PDF is compiled from the supplied LaTeX. Rendered pages are inspected for clipping, overlap, missing mathematical glyphs, and table legibility. References and all displayed constants are checked against the source or exact calculation.

## Outstanding before a public submission

**Repository exclusion audit:** incomplete. The exact current RA-02 and RA-03 statements and omnibus PRs #6 and #32 must be read. All issue states, PR states, conversation comments, review bodies, file patches, and linked solutions must be checked. The supplied audit script does not make a semantic eligibility determination.

**Independent mathematical review:** outstanding. The theorem and code have been self-reviewed in this session, not checked by an independent expert or formal proof assistant. A reviewer should particularly scrutinize the relative Cauchy–Binet asymptotics, the history cancellation, and the unit-diagonal perturbation argument.

**Novelty and priority:** not certified. The search identified the known upper bounds and the stated conjectures, but a failed repository audit cannot establish absence of a previous solution. Do not claim priority until the relevant history and literature are checked.

**Submission metadata:** author/submitter attribution, the repository's exact contribution format, and any maintainer requirements remain to be confirmed. No public issue or pull request has been opened.

## Claims deliberately not made

No solution of RA-01 is claimed. No bound for the expectation of the unsquared RPLU error is claimed. No bounded-condition-number, practical numerical-stability, or average-case assertion is claimed. The archive is not described as having cleared the user's no-existing-solutions condition, as independently peer reviewed, or as representing three elapsed hours of work.
