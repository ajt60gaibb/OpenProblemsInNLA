# PF-04 specification review

Reviewer: OpenAI Codex agent `/root/inventory` (AI), independent of specification author `/root`.

Phase: `specification`. Verdict: **APPROVED**.

Reviewed the complete canonical README, the complete retained `ORIGINAL.md`, and `NUMERICAL_TARGETS.md` before Lean target implementation. Canonical and snapshot bytes match.

- Canonical source SHA-256: `acbf30a432e4ee1898661c05a9efc2f24f9ec32183da33836315b58e6c46e08a`
- Specification input SHA-256: `3294326a93bf021afac3caae3349b01e6f5c23425060cbc22c8cba8c08af1e02`

Factor(A,r) expands the exact entrywise Gram identity A(i,j) = sum_k B(i,k)B(j,k) with real nonnegative B of shape 6-by-r. This is complete positivity, not the weaker doubly nonnegative condition.

Quantifying over all real 6-by-6 A and then assuming an existential finite-width Gram factor admits exactly every completely positive matrix. Symmetry follows from the defining identity; neither strict positivity nor nonsingularity is imposed.

The universal width-nine factor statement is the original explicit equivalent formulation. Arbitrary smaller widths can be padded by zero columns, so exactly nine columns is the original at-most-nine assertion.

The additional existential CP matrix admitting no factor at every natural width r < 9 faithfully retains the displayed maximum-equals-nine formulation and its stated established lower bound. Combined with the universal clause this is precisely a maximum of nine, without a misleading totalized rank on non-CP inputs.

The width-zero empty sum includes A=0 and gives its cp-rank convention correctly. The lower-bound witness is not required positive definite, of full ordinary rank, on the boundary, or of a specified support; these would be unrequested strengthenings.

Numerical constants 6 and 9, non-strict entry nonnegativity, strict comparison r < 9, and exact equality are preserved. No approximate, computational-complexity or certificate claim is inserted. The complete original README is byte-identical to its snapshot.

Independent specification fidelity review only. No Lean implementation, proof, cited-paper verification, or kernel/Comparator run is certified by this review.
