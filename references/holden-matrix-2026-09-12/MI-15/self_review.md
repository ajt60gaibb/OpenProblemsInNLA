# Self-review

The central risk is confusing a small negative numerical eigenvalue with positive semidefiniteness. This pack does not do that. All accepted certificates pass exact integer identities and exact integer strict diagonal-dominance inequalities after a rational congruence.

A separately written verifier constructs the canonical quartic directly from the Toeplitz entry formula and expands every coefficient. It does not merely check the same Gram assembly code against itself. It also verifies the omitted central-coordinate squares, the exact zero directions, dimensions of the complement, and the orientation of the congruence.

The proof that H_num>0 implies T_num invertible is included; invertibility is not inferred from a floating-point factorization. The integer denominator signs are checked. Real-variable and real-coefficient assumptions exactly match the target, and the squares may have real algebraic coefficients as permitted.

The finite cases n=8,...,12 are the only newly certified orders. No extension to all n, novelty priority, independent human review, formal proof-assistant verification, or repository acceptance is claimed. A downstream reviewer should rerun the standard-library checker, alter certificate entries to confirm that invalid data is rejected, and inspect the basis/spanning argument in Sections 3-5.
