# TR-27 border-witness author evidence

Author: AI proof-author agent `/root/reference_review`, acting within the George Stepaniants formalization campaign. This is author evidence, not independent proof review. This agent cannot count as an independent final full-proof referee.

`NLA/TR27/BorderWitness.lean` proves the exact frozen `border_curve_semantics` and `border_two` declarations. It imports Geometry and Mathlib, never Challenge. All frozen mathematical boundary files remain unchanged.

The off-zero cone expression has exactly two entries: `curve(some t)` and `curve(some 0)` with unrestricted complex coefficients `t⁻¹` and `−t⁻¹`. Both entries belong to the complete witness cone by the full-image geometry theorem. The earlier exact divided-difference identity supplies their sum, and the frozen extension-at-zero and nonvanishing properties are included in the complete conjunction.

Every coordinate of the explicit `borderCurve` is represented by a univariate complex polynomial. The substitution algebra homomorphism includes all twelve coordinates, and evaluation is proved to commute with that substitution for every complex parameter, including zero. Given any multivariate polynomial vanishing on every rank-at-most-two cone vector, its substituted polynomial p vanishes at each nonzero complex parameter. The product X*p therefore evaluates to zero at every parameter. Polynomial extensionality over the infinite field ℂ makes X*p the zero polynomial, and the polynomial domain property gives p=0. Evaluation at zero yields vanishing at `witnessVector`.

The final theorem unfolds the exact frozen affine closure: the zero locus of the ideal of all polynomials vanishing on the coordinate image of the full rank-at-most-two set. The proof supplies vanishing for every member of that ideal. It assumes neither a finite sample of equations, a Euclidean closure theorem, nor a curve-local definition of border rank.

A fresh local macOS Lean 4.33.1 rebuild compiles Definitions, Algebra, IntegralImage, Geometry, BorderWitness and an external axiom audit. The audit includes all nine public declarations, including the two definitions. Its retained output and machine-readable receipt record their transitive axiom closures. No `sorry`, `admit`, native-decision call, added axiom, conjectural premise or unproved target assumption appears in the source.

This is bounded local author evidence only. The authoritative Linux verification driver, complete-problem Comparator, completed LeanCert verifier command and independent final full-proof reviews are not claimed here. The full TR-27 campaign still requires complete integration and all remaining target proofs; this receipt does not promote status or publish a problem PR.
