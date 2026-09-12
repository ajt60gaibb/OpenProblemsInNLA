# Research proof pack: intervals and absolute value equations

## Outcome

**Neither unrestricted repository target is claimed resolved.** Both attempted
problems have complete proof candidates for subclass results or reductions,
with exact implementations and certificates. “Complete proof candidate” below describes
an explicitly stated subsidiary theorem, not a complete resolution of its
repository target. Historical novelty is not certified.

| Order | Problem / canonical status | Required classification | Main contents |
|---|---|---|---|
| 1 | AV-03 — open; extreme | **NEW PARTIAL RESULT** | Exact deterministic polynomial-bit solvers for regular lower-Hessenberg AVEs and a triangular subsystem with one feedback variable; an exact optimized-handicap formula; exponential sign-region family; exact Newton-cycle and inverse-hull obstructions; general residual recovery and audited P-LCP reduction. |
| 2 | IV-01 — partially resolved; challenging | **NEW PARTIAL RESULT** | A stronger n=5 sufficient theorem permitting cyclic fixed graphs; a directed fixed-entry graph condition in every dimension allowing both checker parities; SCC cycle normal form for counterexample searches; unconditional nonsingularity, cofactor, and order-two reductions; exact 5 by 5 examples including zero middle minors at both endpoints, with 1255 independently checked minor values across five endpoint matrices. |

## AV-03: proof map

`AV-03/result.md` contains the exact original statement and the complete proof
candidate for Theorem H, with bit-complexity details, reducible blocks, and
zero-coordinate recovery. It also proves the exponential sign-region family,
Newton three-cycle, and inverse-image convex-hull obstruction.

`AV-03/general_reductions.md` proves the general residual-recovery lemma, the
P-LCP equivalence with the exceptional Cayley case handled, and Theorem F for
a second scalar-shooting class. The reduction and nonstationarity observation
are supporting lemmas, not unrestricted algorithms.

`AV-03/optimized_handicap.md` proves, for the three-cycle permutation P and
M_a=I+aP, a>=0,

    kappa*(M_a) = kappa_hat(M_a) = max(0,(a^2-4)/16).

The lower bound holds under every positive diagonal row scaling. Choosing
a=2^m makes the optimized parameter exponential in input bit length even in
dimension three. This is not an algorithmic complexity lower bound; the
corresponding AVEs belong to the polynomially solved subclass.

`AV-03/notes.md` preserves failed approaches and the missing dense-case step.
`AV-03/self_review.md` identifies the strongest scope and arithmetic risks.

## IV-01: proof map

`IV-01/dimension_five_theorem.md` proves Theorem V: in n=5, the full interval
conclusion holds when there are no fixed zero entries and every fully fixed
adjacent 2 by 2 block is nonsingular. Directed fixed-entry cycles are allowed.
For arbitrary larger n, the same argument controls order three only. This
proof is self-contained using the pack's nonsingularity and order-two lemmas.
A cyclic-graph example with both endpoints non-strict is exactly certified.


`IV-01/result.md` contains the exact target and complete proof candidate for
Theorem G. The graph on row and column vertices has an edge for each nonzero
fixed entry, oriented by its checker parity and epsilon_1. Acyclicity, together
with fixed zeros of at most one parity, suffices for the original conclusion.
A forest of nonzero fixed entries is a concrete mixed-parity subclass.

The theorem explicitly invokes Adm--Garloff (2026), Theorem 3.3, after an exact
positive diagonal scaling. Its limit step uses a separately proved
nonsingularity lemma; this is not assumed from nonsingular approximants.

`IV-01/cycle_reduction.md` removes noncyclic nonzero fixed edges from a
putative counterexample without removing its wrong-sign minor. Directed cycles
and fixed zeros of both parities remain unresolved.

The stronger rational 5 by 5 example has signature (+,+,-,+,-), a vanishing
order-two minor at its lower checker endpoint and a vanishing order-three
minor at its upper endpoint. Neither endpoint is strictly SR. There are two
fixed entries of opposite parities and 23 independent nonfixed entries. The
theorem certifies the full real interval. A simpler first example is also
retained, with its one-strict-endpoint limitation explicitly discussed.
Sampling is not used as the proof.

`IV-01/order_two_reduction.md` additionally proves that all order-two signs
are already controlled by the original hypotheses. Together with the
nonsingularity/cofactor reduction, this leaves only orders 3,...,n-2; in
dimension five, only order three remains.

`IV-01/notes.md` and `IV-01/self_review.md` preserve the search, failed common
smoothing approach, limitations, and precise verification priorities.

## Reproduce

From this directory, run:

```sh
python verify_pack.py
```

The core proofs and tests require Python's standard library only. This command
recreates test logs and checks the supplied certificates. Per-problem scripts
can also be run independently. See `README.md` for the file inventory and
`source_notes/SOURCES.md` for source URLs and canonical blob identifiers.

## Acceptance and evidence

No repository write, status update, formal proof-assistant verification, or
acceptance is claimed. Exact regression tests are distinguished from the
universal mathematical proofs. The two complete original questions remain
open within this pack; the supplied subsidiary proof candidates are intended
for adversarial verification and priority checking.

## Final exploration of uncovered cases

Two exact searches with a fixed singular leading 2 by 2 block, outside both
Theorem G and Theorem V, checked 11,136 sampled interval vertices (with possible
repetition) and found no counterexample. The scripts, exact trajectories, and
logs are retained in IV-01. This component alone is EXPERIMENTAL EVIDENCE ONLY;
it does not change the NEW PARTIAL RESULT classification or fill the remaining
unrestricted gap.
