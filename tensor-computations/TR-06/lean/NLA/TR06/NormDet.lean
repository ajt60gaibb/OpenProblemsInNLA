/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.MeasureTheory.Function.Jacobian
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory
open MeasureTheory Set

namespace NLA.TR06.Area

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Rectangular Jacobian expressed as the square root of the Gram determinant. -/
theorem normDet_eq_sqrt (A : E →L[ℝ] F) :
    A.toLinearMap.normDet = Real.sqrt (A.adjoint.comp A).det := by
  rw [← A.normDet_sq]
  exact (Real.sqrt_sq A.toLinearMap.normDet_nonneg).symm

/-- The rectangular Jacobian varies continuously with the derivative. -/
theorem continuous_normDet :
    Continuous (fun A : E →L[ℝ] F => A.toLinearMap.normDet) := by
  simp_rw [normDet_eq_sqrt]
  exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
    (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))

#print axioms normDet_eq_sqrt
#print axioms continuous_normDet
#assert_trust kernel normDet_eq_sqrt
#assert_trust kernel continuous_normDet

end NLA.TR06.Area
