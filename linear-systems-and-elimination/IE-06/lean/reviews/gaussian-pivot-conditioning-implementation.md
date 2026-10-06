# F7 implementation receipt

Exact frozen source: `NLA/IE06/GaussianPivotConditioning.lean`.
SHA-256: `b51ea35db8301d3001422be174ce67640337fae3e3c5203ccf4d774bdb33b946`.

The implementation satisfies all four approved stages of `gaussian-pivot-conditioning-contract.md`: original-label pivot partition and fixed-coordinate product law; measurable linear residual/slab geometry, positive Gaussian mass and null boundary; strict/closed actual-fiber sandwich and selected-block goodness almost everywhere; exact restricted pushforward and tested integral factorization, followed by normalized adaptive transfer with no pivot-order counting loss.

`fixed_order_restricted_law` identifies the pushforward of the actual Gaussian matrix measure restricted to the literal canonical pivot-order event with the fixed Gaussian coordinate product restricted to Good(T) and the remaining-row slabs. `fixed_order_lintegral` keeps the exact factor q(T)^(n-t). `orderWeights_sum_one` proves the true finite partition weights sum to one. `adaptive_event_le` consequently retains the same epsilon bound for a jointly measurable family of fiber events. No conditional-law or independence premise is inserted.

The approved reuse route proves `actual_good_ae` from the existing Gaussian nonsingularity and GaussianTies theorem. Good(T) is never asserted for almost every unselected square Gaussian block. Fixed-coordinate Fubini and the proved null slab boundaries then give `orderEvent_ae_eq_fiber`; this replaces a duplicate triangular-polynomial exceptional-fiber proof without adding an assumption. The square block law is written as `gaussianMatrix t`, definitionally the same literal row Gaussian product as `GaussianNull.gaussianRect t t`, to keep Lean's matrix measurable-space elaboration uniform.

The final deterministic interpretation is also proved: the upper factor is triangular with nonzero determinant under the exact nonzero-pivot premise, residual telescoping gives lambda(T,x) U(T)=x, and `truncationBody_eq_inverse_upper` identifies the body with all coordinates of x U(T)^(-1) bounded by one. Singular blocks retain totalized divisions throughout all unconditional geometry and measure theorems.

Validation: Lean 4.33.1 compilation exited 0 with zero warnings. All 86 owned declarations have individual `#assert_trust kernel` checks and `#print axioms` outputs. The only reported axioms are propext, Classical.choice and Quot.sound; there is no sorry, custom axiom, native computation or manuscript theorem premise. The full log and machine-readable receipt are retained in `reviews/gaussian-pivot-conditioning/`. All dimensions including t=0 and t=n are part of the literal quantified statements. Independent source review remains the next gate before this module is treated as reviewed.
