# IV-01 research notes

## Main additional result

Positive row and column scalings preserve every minor's sign and zero status.
At a fixed nonzero entry, their first-order checker-gap requirement becomes a
strict inequality r_i+c_j of a prescribed sign. Writing these as comparisons
between row and column potentials gives the directed graph in Theorem G.
Acyclicity is exactly the feasibility condition for this strict scaling
strategy. Integer powers (1+t)^(r_i+c_j), rather than only first-order
approximations, give an exact sign-preserving perturbation.

This opens every nonzero fixed entry when the graph is acyclic; any fixed
zeros remain. The verified external same-parity theorem then applies when
these remaining zeros have one parity. Nonsingularity in the limiting interval
requires the separate inverse-positive box lemma; it must not be inferred
from a limit of nonsingular approximants.

## Boundary search and the exact example

A hierarchical symmetric Vandermonde kernel was used to obtain strict
signature (+++-+) in dimension five. Exact coordinate bounds, computed from
affine dependence of each minor on one entry, found the lower permissible
value of entry (1,1). At that boundary the leading order-three minor is exactly
zero and the other 250 minors retain strict correct signs. A small rational
checker-positive perturbation outside two fixed positions gives the second
endpoint. Both fixed parities occur, and the fixed graph is a two-edge path.

`build_and_verify_example.py` repeats the construction rather than merely
loading rounded matrices. All 251 endpoint minors are exported individually.
`test_graph_and_certificates.py` independently recomputes them by Leibniz
expansion, using neither the discovery determinant routine nor its Gaussian
elimination. The 24 sampled interval matrices are supplementary tests only;
the theorem, not sampling, certifies the continuum of interval matrices.

## Failed or incomplete approaches

**Common totally-positive smoothing.** Multiplication by a common strictly
totally-positive matrix does not generally preserve checker ordering. For
example, take A=I_2, B=diag(2,1), and
C(t)=[[1,t],[t,1+t^2]], t>0. Both A and B are nonsingular totally nonnegative,
and C(t) is strictly totally positive. But C(t)(B-A) has entry (2,1)=t>0,
which has the wrong checker sign. This is only an obstruction to that
approximation argument, not a counterexample to the interval conjecture.

**Inversion.** Endpoint cofactor signs yield inverse positivity after a
checkerboard conjugation and a common scalar sign. This proves nonsingularity
and the required cofactor signs throughout every original interval. It does
not supply the missing middle-order minors. Applying inversion again merely
changes the signature by the complementary-minor formula; no general new
interval theorem follows automatically.

**Generic strict perturbations.** Random strictly SR endpoint pairs cannot
address the remaining gap, since their interval property is already known.
The search therefore moved to exact boundary matrices with zero middle
minors. The single boundary example obtained is a positive subclass example,
not a counterexample. No exhaustive counterexample search is claimed.

**Directed cycles.** An alternating fixed rectangle makes the diagonal
potential inequalities inconsistent. This is an obstruction to the chosen
scaling, not to the original conjecture. A positive singleton interval already
illustrates that cycles can coexist with the desired property.

## Strongly connected component normal form

`cycle_reduction.md` shows how to open all noncyclic nonzero fixed edges while
leaving the cyclic edges and fixed zeros unchanged. A strictly wrong-sign
minor would persist under sufficiently small perturbations, so a putative
counterexample can be reduced to that cyclic normal form. `scc_reduction.py`
implements and tests the graph construction. It does not decide the conjecture.

## Remaining gap and next concrete targets

The surviving cases have directed cycles among nonzero fixed entries, fixed
zero entries of both parities, or both. A promising next exact search is a
five-dimensional (+++-+) boundary pair with one alternating fixed rectangle
and several simultaneous vanishing middle minors. A structural proof would
need to eliminate the cyclic scaling obstruction using additional
sign-regularity identities, rather than treating graph infeasibility as a
counterexample. Another possible route is a higher-order compatible
regularization for fixed zero entries, for which diagonal scaling alone has
no effect.

The main graph theorem is a derived sufficient condition with a full proof
candidate. Its historical priority has not been established; it explicitly
uses the previously published same-parity theorem.

## Final refinements from the adversarial review

An audit noticed that the first boundary example has one strictly SR endpoint.
That case has a simpler enlargement argument, as recorded in result.md. A
second example was therefore constructed with signature (++-+-), a zero
order-two minor at A and a zero order-three minor at B. It has the same
mixed-parity fixed forest but neither endpoint is strictly SR.

An attempted monotone coordinate extension for the first signature (+++-+)
hit a zero full determinant in all 23 free coordinate directions; its exact
search data are retained in both_boundary_search_attempts.json. This was not
a counterexample and was not used as a theorem. Changing to (++-+-) yielded
the both-boundary example directly. both_boundary_discovery.json preserves
the exact intermediate discovery; the reconstruction script independently
recreates the final data.

The final unconditional reduction proves that order-two signs cannot fail
under the original hypotheses. Thus a targeted n=5 search need only seek a
wrong-sign order-three minor. Its proof is in order_two_reduction.md; the
finite binary regression is in verify_order_two.py. The stronger order-two
statement is not claimed historically new without a priority search.

## Dimension-five refinement

The strict relative-interior order-two argument led to Theorem V. Absence
of fixed zeros makes every relative-interior entry positive. A zero adjacent
order-two determinant with a free entry could be made negative by an arbitrarily
small one-coordinate change, contradicting the unconditional order-two theorem.
Thus only a fully fixed singular adjacent block can obstruct strict order two.
A two-stage projective secant-slope argument propagates weak order-three signs
from adjacent triples when order two is strict. The result covers cyclic fixed
graphs in dimension five and narrows the search to fixed zeros or fully fixed
singular adjacent 2 by 2 blocks.

For general dimension, a possible next route is a higher-order analogue of the
strict-order-two propagation lemma. No such general propagation theorem is
proved in this pack, and no induction to all middle orders is claimed.

## Final targeted search beyond the sufficient conditions

`search_fixed_singular_block.py` fixes the leading singular 2 by 2 block of
the (++-+-) endpoint, so neither Theorem G nor Theorem V applies. It constructs
new checker-upper endpoints by exact coordinate bounds while retaining the
same SR signature and nonsingularity, then tests selected interval vertices
for a wrong-sign order-three minor using integer arithmetic after common
scaling. Two completed deterministic-seed runs (20260912 and 20260914) performed
64 endpoint checks, 11,136 sampled-vertex checks, and 1,113,600 order-three
minor checks. These counts include possible repeated vertices. No witness was
found. This finite exploration does not prove the remaining implication.

The JSON logs record every endpoint update, rational shift, seed, and count.
Reproduce them with the parameters recorded in the logs. A more aggressive
seed-20260913 run (12 restarts, 8 steps, 256 vertices per endpoint) exceeded a
40-second execution limit before writing its final log; no result or partial
count from that interrupted run is included in the claimed checks. The two
completed runs and all theorem/certificate checks finished successfully.
