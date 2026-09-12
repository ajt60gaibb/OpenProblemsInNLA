# IV-01 self-review

## Classification

NEW PARTIAL RESULT. The unrestricted original implication is neither proved
nor disproved. Theorem G imposes an additional directed-acyclic condition and
a restriction on fixed zero entries. It must not be labeled a complete solution
to IV-01. Graph cycles are not counterexamples.

## Most important proof checks

1. The original matrix field is real, not merely rational. The scaling,
   continuity, and inverse-positive arguments are over the reals. The rational
   example is only a certificate illustrating the theorem.
2. All orders of minors, the same endpoint signature, and endpoint
   nonsingularity are retained. Zero minors are allowed. Positive diagonal
   scaling preserves both zero and nonzero minors exactly.
3. The orientation uses epsilon_1 times checker parity. It is not correct to
   omit epsilon_1 when endpoint entries are negative. Tests cover that reversal.
4. Fixed zero entries cannot be opened by positive diagonal scaling. The
   forest corollary explicitly assumes all fixed entries are nonzero. The
   broader theorem permits fixed zeros only when they all have one parity.
5. Original strict gaps persist for one common sufficiently small t because
   the number of entries is finite. The proof makes no uniform lower-gap or
   rational-bit assumption for the real-matrix theorem.
6. Relative-coordinate interpolation works for both signs of B_ij-A_ij.
   At original fixed entries theta=0 is valid; M(t) tends to the original M.
7. Continuity alone proves only nonnegative signed minors. Nonsingularity of
   the limiting M follows separately from Lemma N. This closes an otherwise
   serious limit gap.
8. The inverse-positive box lemma has the factor order
   C=Q(I-Q^-1 E), C^-1=(I-Q^-1 E)^-1 Q^-1. Its positive vector argument
   establishes a genuine norm bound strictly less than one. The delta=-1
   case reverses and negates the two checker-conjugated endpoints.
9. The external input is Adm--Garloff (2026), Theorem 3.3, not their strict-only
   Theorem 3.2. Its full same-parity hypothesis and nonsingular SR conclusion
   were checked against the primary HTML publication. Downstream verification
   should recheck that exact theorem and its conventions.
10. The SCC reduction preserves a strictly negative signed minor of a putative
    witness; it does not infer that any witness exists. Rationality is claimed
    only when endpoints and witness are rational and t is chosen rational.

## Certificate audit

All 1255 minor values across the five distinct endpoint matrices were independently recomputed by direct Leibniz
expansion and matched the exported elimination-based certificates exactly.
The vanishing leading 3 by 3 minor is an exact zero, not a numerical tolerance.
Graph-only edge-case test matrices are explicitly not asserted to be SR.
No finite set of interval samples is used as a proof of the universal result.

## Remaining verification priorities

Check the graph-to-potential sign convention, the special role of fixed zeros,
and the independent nonsingularity step before polishing. Determine historical
priority of this graph formulation; the pack makes no exhaustive novelty claim.
No proof assistant or formal repository acceptance is claimed.

## Additional checks on the final reductions

The first example's one-strict-endpoint simplification is explicitly disclosed.
The stronger example has a zero middle minor at each endpoint and is audited
independently. The order-two proof uses nonsingularity only to obtain a positive
perfect matching and then a positive diagonal by uncrossing; it does not assume
that all intermediate matrices are nonsingular under its weaker hypotheses.
Staircase propagation uses the opposite checker parity of immediate neighbors.
The telescoping product cancels only in a rectangle whose entries have first
been proved strictly positive. The normalization for epsilon_2=-1 reverses
rows and, where necessary, swaps endpoint roles. These details should be checked
before using the reduction to assert that only order three remains when n=5.

## Theorem V review

The relative interior is taken with respect to the actual box, not the full
matrix space. Nonfixed intervals whose endpoint is zero still have positive
relative interiors after normalization; a fixed zero is expressly excluded.
The proof of strict adjacent order two varies just one free entry, whose
cofactor is nonzero because every relative-interior entry is positive. This
would contradict the already proved weak order-two theorem, not an unproved
strictness assertion. The projective propagation lemma has two stages: first
all row triples for consecutive columns, then all column triples for arbitrary
rows. Positive denominators follow from strict order-two signs. The final
limit step again uses Lemma N for nonsingularity. The full conclusion is only
for n=5; for larger n the theorem establishes order three, not all orders.
