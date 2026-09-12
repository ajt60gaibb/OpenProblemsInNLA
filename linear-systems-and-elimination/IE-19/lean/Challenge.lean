/- Independently reviewed target environment for Comparator.
The deliberate placeholders below are never imported by the solution. -/
import NLA.IE19.Definitions

set_option autoImplicit false
namespace NLA.IE19

theorem counterexample :
    Admissible 1 1 witness ∧
    IsUnit witness.det ∧
    IsUnit (comparisonMatrix (n := 3) 1 1).det ∧
    rowSumNorm witness⁻¹ = 7 / 9 ∧
    rowSumNorm (comparisonMatrix (n := 3) 1 1)⁻¹ = 5 / 4 ∧
    rowSumNorm witness⁻¹ < comparisonBound 3 1 1 := by
  sorry

theorem not_lowerBoundConjecture : ¬ LowerBoundConjecture := by
  sorry

theorem not_sharpConjecture : ¬ SharpConjecture := by
  sorry

end NLA.IE19
