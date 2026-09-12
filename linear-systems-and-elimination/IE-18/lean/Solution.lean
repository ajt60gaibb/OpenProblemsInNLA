/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's IE-18 counterexample.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.IE18.Proof

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
      squaredNorm witnessInitial = 1920682 / 21289638243 :=
  residual_certificate_proved

theorem counterexample :
    ∃ hM : witnessMatrix.IsHermitian,
      witnessMatrix ≠ 0 ∧
      (1 : ℝ) ∉ spectrum ℝ witnessMatrix ∧
      witnessMatrix.PosDef ∧ (1 - witnessMatrix).PosDef ∧
      spectrum ℝ witnessMatrix = Set.range witnessEigenvalues ∧
      witnessInitial ≠ 0 ∧
      pairMaximum hM = 1 / 121 ∧
      pairMaximum hM < amplification witnessMatrix witnessInitial ∧
      ¬ IsGreatest (amplificationSet witnessMatrix) (pairMaximum hM) :=
  counterexample_proved

theorem not_fourStepConjecture : ¬ FourStepConjecture :=
  not_fourStepConjecture_proved

#assert_trust kernel residual_certificate
#print axioms residual_certificate
#assert_trust kernel counterexample
#print axioms counterexample
#assert_trust kernel not_fourStepConjecture
#print axioms not_fourStepConjecture

end NLA.IE18
