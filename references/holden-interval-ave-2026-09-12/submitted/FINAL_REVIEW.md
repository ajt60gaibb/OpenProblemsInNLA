# Final audit record

Final clean-copy verification: 2026-09-12T20:01:46.552772+00:00.
Recorded research-window start: 2026-09-12T17:03:53Z.
These are wall-clock records, not CPU-time or asynchronous-execution claims.

All ten core exact suites passed both in the source directory and again after
extracting the ZIP into a separate clean directory. Reproduction does not
depend on the source directory's absolute path or cached bytecode. The archive
contains no font files, external binaries, or required third-party Python packages.

The final classifications remain NEW PARTIAL RESULT for AV-03 and IV-01.
Complete proof candidates are provided only for the expressly delimited
subsidiary theorems. Neither unrestricted repository target is declared solved.
No repository status was modified and no formal acceptance is claimed.

The main final additions are the exact cyclic optimized-handicap formula and
Theorem V for dimension five. Theorem V permits cyclic fixed-entry graphs but
excludes fixed zero entries and fully fixed singular adjacent 2 by 2 blocks.
For larger dimensions it controls order three, not all remaining orders.
The graph theorem G has its own explicit assumptions and uses the checked
external same-parity theorem. No external theorem is needed for the
order-two and dimension-five arguments beyond the elementary proofs supplied.

The finite verification record comprises 192 exact AVE solver cases, 10,116
exact handicap margin checks, 1,255 independent Leibniz comparisons of minor
values, exact graph and sign-itinerary certificates, and the finite binary
order-two regression. The two additional exploratory searches used 11,136
sampled interval vertices and found no witness; their absence of a witness is
not a proof. One interrupted exploratory run is disclosed in IV-01/notes.md.

Priority and formal-proof review remain downstream tasks. In particular,
self-contained derivations in this pack are not a guarantee of historical
novelty. The written universal arguments, not the finite tests, are the basis
of the subsidiary proof candidates.
