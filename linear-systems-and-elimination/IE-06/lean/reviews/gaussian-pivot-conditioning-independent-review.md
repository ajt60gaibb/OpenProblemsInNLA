# Independent review of the actual GEPP conditioning law

Root read all 1279 lines of the source by /root/source_statement_author,
SHA-256 `b51ea35db8301d3001422be174ce67640337fae3e3c5203ccf4d774bdb33b946`,
and independently compiled that exact source with the pinned Lean 4.33.1
runtime. Compilation exited zero. Every owned declaration has a kernel trust
assertion; reported axioms are limited to propext, Classical.choice,
and Quot.sound.

The selected labels are the actual accumulated row-swap permutation. Their
finite partition is exhaustive and disjoint even for singular matrices.
The fixed selected/remaining coordinate map is proved to have the exact
product Gaussian law, without adaptive conditioning at this step. The
residual linear maps use the actual no-pivot selected block; the active
coordinate induction checks that these agree with the canonical trajectory.

The multiplier body is closed, convex, symmetric, has positive mass even
for singular totalized blocks, and its strict/closed difference is null.
The proof correctly treats a zero linear functional at a nonzero boundary
level as an empty null event. Strict fiber constraints force the prescribed
order, while actual maximal pivots give the closed constraints. The internal
Good(T) condition is proved for the actual selected block almost everywhere
using the existing nonsingularity and distinct-magnitude results; it is not
incorrectly asserted for an arbitrary unselected block.

These facts prove the exact restricted pushforward measure, then Fubini and
normalization retain q(T)^(n-t) in the tested integral. Finite partition
weights sum to one; the adaptive event transfer therefore introduces no
factor for the number of orders. The final telescoping argument identifies
multipliers with x U(T)^(-1) under explicit nonzero pivots. Empty selected
and remaining blocks retain their literal quantified meanings.

Approved exact statements and proofs. The later truncated-inverse
application must still prove the elimination/selected-block representation
and joint measurability of its actual events. This review does not assert
the completed IE-06 probabilistic proof.
