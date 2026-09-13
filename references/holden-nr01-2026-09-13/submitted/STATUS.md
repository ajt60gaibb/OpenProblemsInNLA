# Status of the result

**Overall NR-01 status: PARTIAL.**

## Established by the new argument

The report supplies a computer-assisted proof draft that the real nonnegative
rank is exactly nine for the regular 17-, 18-, 19-, and 20-gon slack matrices.
It rules out every eight-term factorization through a rank-balanced geometric
reduction, a degeneration-safe finite cover, and exact linear/quadratic
algebra. Four exact nine-term factorizations establish the matching upper
bounds.

The finite result includes arbitrary real factors, not just symmetric,
rational, or algebraic factors. Genericity is used only in an intermediate
perturbation argument, not imposed on a hypothetical exact lift.

## What is new relative to the preceding package

The preceding report left 8 <= rank_+(S_17) <= 9. The new argument rules out the
value eight for n=17 and additionally resolves n=18,19,20. The earlier exact
ranks eleven for n=43..48 are retained, not newly reproved by the finite
classification argument.

## What is not established

There is no universal equality proof, no induction across polygon sizes, and
no new general doubling lower-bound recurrence. In particular, the package
still leaves 9 <= rank_+(S_n) <= 10 for n=25..30 and 10 <= rank_+(S_n) <= 11 for
n=33..42. A hypothetical nine-term factorization can require a five-dimensional
nine-facet lift, beyond the eight-facet catalogue used here.

No implication is drawn from a numerical search failing to find a
factorization. No implication of the form "no finite-field point, hence no
real point" is used. The finite-field step instead transfers nonzero minors
and combines them with a characteristic-zero structural upper bound on the
quadratic row-space dimension.

## Verification boundary

The complete geometry stage, all six algebra stages, the exact upper/control
stage, and thirteen regression tests passed. The six algebra stages contain
13,220 successful pattern-prime checks. Release verification was completed in
separate processes/stages; `checks/release/summary.json` assembles their saved
records. The summary command itself is not an arithmetic verification.

The result has not been independently peer reviewed or formalized in a proof
assistant. Bibliographic novelty has not been established by an exhaustive
priority investigation. Treat it as a shareable, reproducible research proof
draft whose mathematical reductions and implementation remain open to audit.
