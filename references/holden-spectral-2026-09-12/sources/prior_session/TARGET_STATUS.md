# Target-by-target accounting

The category had 13 open targets at the pinned snapshot: seven OPEN and six
PARTIAL. The requested priority is recorded below: OPEN before PARTIAL, then
challenging before extreme, with ID order as a tie-breaker. Reading and triage
followed that order. Subsequent proof work was concentrated on routes that
produced checkable partial results. This is not a claim of a full proof attempt
or equal research time on every entry.

| Order | ID | Snapshot status | Difficulty | Actual outcome in this bundle |
|---:|---|---|---|---|
| 1 | IS-01 | OPEN | challenging | Statement and boundary scope inspected; no full proof or counterexample. |
| 2 | KE-02 | OPEN | challenging | Complete weak-coupling subclass construction and unrestricted order-two construction; full target unmet. |
| 3 | SP-01 | OPEN | challenging | Statement and generic interlacing hypothesis inspected; no endpoint-threshold proof. |
| 4 | SP-02 | OPEN | challenging | Statement and off-diagonal endpoint inspected; no proof at the requested universal threshold. |
| 5 | SP-03 | OPEN | challenging | Complete skew-multiplier reduction; known order-one count rederived; general degree not evaluated. |
| 6 | IE-07 | OPEN | extreme | Constructive regularization and runtime requirements inspected; no qualifying deterministic algorithm. |
| 7 | SP-07 | OPEN | extreme | Complete constant-one bound for the two-point-spectrum subclass via the SP-09 manuscript; global sharp constant undetermined. |
| 8 | IS-04 | PARTIAL | challenging | Existing reviewed prime-square construction and surviving all-orders bound inspected; no completion. |
| 9 | SP-08 | PARTIAL | challenging | Complete general pattern reduction and exact finite cases `(8,1/2)`, `(10,0)`, `(11,0)`; general conjecture unmet. |
| 10 | SP-09 | PARTIAL | challenging | Complete finite-amplification invariance for the two-point-spectrum subclass; unrestricted normal pairs unmet. |
| 11 | IS-05 | PARTIAL | extreme | Existing exponent interval `17/92 <= alpha_* <= 1/2` inspected; no matching construction or exact exponent. |
| 12 | SP-10 | PARTIAL | extreme | Original minimum-rank complement target and recorded subclasses inspected; no general proof or counterexample. |
| 13 | SP-14 | PARTIAL | extreme | Continuous-symbol/one-sided-annulus formulation inspected; no general canonical-distribution proof. |

## Reasons the limited results do not close the original targets

KE-02 requires arbitrary normalized tridiagonal inputs, not a coupling of order
`delta/n`. SP-03 requires an all-ranks degree, not merely equivalent equations.
SP-07 asks for one sharp constant over every normal pair. SP-08 quantifies over
all dimensions and interval parameters. SP-09 allows both matrices to have
arbitrarily many distinct eigenvalues. Those missing quantifiers and hypotheses
are substantial; they cannot be removed by relabeling a special case.

For the remaining entries, inspection and mathematical triage did not yield a
completed argument for the actual target. No resolution is inferred from an
unrelated older conjecture, an already-recorded result, or an unsuccessful
counterexample search. The deliverable does not assert that no subsequent
solution exists anywhere in the literature.

## Session history

The original assistant attempt failed and produced no deliverable. The later
reminder marked a time limit; it did not demonstrate background research.
This recovery pass accessed the repository in the current response, generated
proofs and certificates, and packaged them for review. No unattended three-hour
session, timer-controlled background research, or continued work after delivery
is claimed. Exact current-pass start and packaging timestamps are recorded in
`session.json`.
