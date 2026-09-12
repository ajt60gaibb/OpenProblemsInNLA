/- Target environment for independent statement review and Comparator.
The deliberate placeholders below must never be imported by the solution. -/
import NLA.IE18.Definitions

set_option autoImplicit false
namespace NLA.IE18

theorem residual_certificate :
    witnessInitial ≠ 0 ∧
    squaredNorm ((1 - witnessMatrix).mulVec witnessInitial) = 61 / 50 ∧
    residualCoefficient witnessMatrix witnessInitial = 90 / 61 ∧
    residualMap witnessMatrix witnessInitial = witnessFirst ∧
    witnessFirst ≠ 0 ∧
    squaredNorm ((1 - witnessMatrix).mulVec witnessFirst) = 1381 / 93025 ∧
    residualCoefficient witnessMatrix witnessFirst = 3140 / 1381 ∧
    fourStepResidual witnessMatrix witnessInitial = witnessSecond ∧
    squaredNorm (fourStepResidual witnessMatrix witnessInitial) /
      squaredNorm witnessInitial = 1920682 / 21289638243 := by
  sorry

theorem counterexample :
    ∃ hM : witnessMatrix.IsHermitian,
      witnessMatrix ≠ 0 ∧
      (1 : ℝ) ∉ spectrum ℝ witnessMatrix ∧
      witnessMatrix.PosDef ∧ (1 - witnessMatrix).PosDef ∧
      spectrum ℝ witnessMatrix = Set.range witnessEigenvalues ∧
      witnessInitial ≠ 0 ∧
      pairMaximum hM = 1 / 121 ∧
      pairMaximum hM < amplification witnessMatrix witnessInitial ∧
      ¬ IsGreatest (amplificationSet witnessMatrix) (pairMaximum hM) := by
  sorry

theorem not_fourStepConjecture : ¬ FourStepConjecture := by
  sorry

end NLA.IE18
