import NLA.IE06.Definitions

/-! Complete propositions only. Defining a proposition does not prove it.
The original statement is preserved verbatim in source/original-HEAD-README.md.
All probability values below are in ℝ≥0∞, without a lossy toReal conversion. -/

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Topology
open Filter
noncomputable section

namespace NLA.IE06

/-- IE-06 in full: the square-root upper exponent for exact all-Schur GEPP
growth of a standard Gaussian matrix, with every admissible tie path covered.
This definition is a statement, not an assertion that the limit is proved. -/
def SquareRootUpperBound : Prop :=
  ∀ η : ℝ, 0 < η →
    Tendsto (fun n : ℕ => gaussianMatrix n
      (exceedanceEvent n ((n : ℝ) ^ ((1 : ℝ) / 2 + η)))) atTop (𝓝 0)

/-- A stronger all-Schur tail extracted from the argument in Urschel v1,
Section 5.1 and Proposition 5.1's proof. This is NOT the literal LU-growth
statement of Theorem 1.4. The constants depend only on α. The complete proof, including the source-to-Schur, normalization and
almost-sure tie bridges, is supplied in Unconditional.lean. -/
def SchurSubpolynomialTail : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      gaussianMatrix n (exceedanceEvent n
        (Real.sqrt (n : ℝ) * Real.exp (C * Real.sqrt (Real.log (n : ℝ))))) <
        ENNReal.ofReal ((n : ℝ) ^ (-α))

#assert_trust kernel SquareRootUpperBound
#assert_trust kernel SchurSubpolynomialTail
#print axioms SquareRootUpperBound
#print axioms SchurSubpolynomialTail

end NLA.IE06
