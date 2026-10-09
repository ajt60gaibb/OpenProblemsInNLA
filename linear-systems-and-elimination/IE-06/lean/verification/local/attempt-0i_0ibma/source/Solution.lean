import NLA.IE06.Unconditional

/-! Concrete implementations of all six independently frozen Challenge
signatures. This module does not import the reference declarations. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open MeasureTheory
noncomputable section
namespace NLA.IE06

theorem squareRootUpperBound : SquareRootUpperBound := squareRootUpperBound_proved

theorem schurSubpolynomialTail : SchurSubpolynomialTail := schurSubpolynomialTail_proved

theorem gaussianMatrix_probability (n : ℕ) :
    IsProbabilityMeasure (gaussianMatrix n) := gaussianMatrix_probability_proved n

theorem exceedanceEvent_measurable (n : ℕ) (t : ℝ) :
    MeasurableSet (exceedanceEvent n t) := exceedanceEvent_measurable_proved n t

theorem admissiblePath_exists {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    ∃ path : PivotPath n, AdmissiblePath A path := admissiblePath_exists_proved A hA

theorem gaussianMatrix_singular_null (n : ℕ) :
    gaussianMatrix n {A : Mat n | A.det = 0} = 0 := gaussianMatrix_singular_null_proved n

#assert_trust kernel squareRootUpperBound
#assert_trust kernel schurSubpolynomialTail
#assert_trust kernel gaussianMatrix_probability
#assert_trust kernel exceedanceEvent_measurable
#assert_trust kernel admissiblePath_exists
#assert_trust kernel gaussianMatrix_singular_null
#print axioms squareRootUpperBound
#print axioms schurSubpolynomialTail
#print axioms gaussianMatrix_probability
#print axioms exceedanceEvent_measurable
#print axioms admissiblePath_exists
#print axioms gaussianMatrix_singular_null
end NLA.IE06
