# Notes

The original handoff did not preserve an order-eight Gram matrix. These are newly generated certificates, not a reconstruction of missing entries claimed in that archive.

The naive wedge Gram Q_0 is indefinite. Adding arbitrary Plücker corrections and minimizing its negative eigenvalues stalled near a singular face. One forced zero diagonal occurs at the wedge indexed (-(n-1),n-1). Positive semidefiniteness then requires that entire row vanish. Enforcing it alone leaves further singular directions; in order eight, a fixed saturated 2-by-2 principal minor already forces the sum of the wedges (-7,6) and (-6,7) into the kernel.

The successful ansatz imposes the disjoint-support kernel vectors (8) in `proof.md` for k=0,...,n-2, solves the resulting affine equations exactly, and optimizes only the remaining parameters. No claim that every possible Gram representation has those kernels is needed: one valid certificate is enough for each fixed order.

For orders 8-12 the search found positive definite matrices on the remaining complement. Rounding only the independent free parameters to multiples of 10^-6, then reconstructing all constrained parameters exactly, preserved every kernel identity. An approximate inverse Cholesky factor was rationalized to a denominator-10^9 congruence. Its output was accepted only after exact strict diagonal dominance was verified.

The failed pre-facial optimization, final floating-point matrices, exact affine parameter expressions, and generator scripts are archived. The retained numerical eigenvalues are discovery diagnostics, never the positivity proof.

Promising all-order direction: exploit the separation between same-sign wedges and mixed-sign wedges. The commutator vanishes for same-sign Toeplitz shifts, while Plücker corrections transfer quadratic terms between these sectors. A uniform analytic choice of corrections would be more valuable than merely extending the finite-order search. No such choice or induction is proved here.
