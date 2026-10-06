# Independent review of exact selected-block elimination coordinates

Root read the complete 319-line source by /root/independent_math_review,
SHA-256 `8878c320c99fda38e3ef5e6268071238b5f5e65579cb2a902e049e3e43cd3eca`.

The stronger prefix-only nonzero-pivot premise is sufficient: exact column
annihilation uses only those denominators. Constructing U=C*T from actual
no-pivot elimination rows proves det(T) nonzero from the triangular upper
factor without presuming invertibility. The remaining-coordinate induction
tracks the accumulated original-label permutation, so the active row retains
exactly its own unselected identity coordinate. Annihilation of the first t
original columns then determines the selected coefficients as -z*T^-1.

The final row identity is in original input coordinates. Its identity label
is outside the selected injection, and the squared norm proof explicitly
sums over those disjoint coordinates, yielding exactly 1+||z*T^-1||^2.
Inactive rows remain zero by the existing semantics. Full nonsingularity
corollaries and the fixed-fiber Good-to-prefix-nonzero bridge use their
correct directions. Empty stages are included.

Approved exact statements and proofs. Root independently compiled the exact source: all eighteen kernel checks
passed, only foundational axioms occur, and no warnings were emitted. No random basis choice or probabilistic premise is introduced.
