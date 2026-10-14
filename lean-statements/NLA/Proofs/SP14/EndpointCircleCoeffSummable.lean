import NLA.Proofs.SP14.EndpointTwoSidedCoefficient
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
Absolute summability of the physical coefficients at the exponents used by
the canonical endpoint construction. The circle realization is a later gate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private theorem summable_endpointCircleWeight_norm_sq
    (r : ℝ) (hrHalf : (1 / 2 : ℝ) < r) :
    Summable (fun n : ℕ =>
      ‖(Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (-r)))‖ ^ 2) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * r)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-2 * r)) := by
    simpa [Nat.cast_add] using (summable_nat_add_iff 1).2 hbase
  convert hshift using 1
  ext n
  have hn : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn _)]
  rw [← Real.rpow_mul_natCast hn.le (-r) 2]
  congr 1
  ring

/-- The scalar Sobolev weight is a square-summable complex sequence for
`r>1/2`. -/
noncomputable def endpointCircleWeightLp (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) : SobolevCoeff r :=
  ⟨fun n : ℕ => Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (-r)), by
    apply memℓp_gen
    simpa using summable_endpointCircleWeight_norm_sq r hrHalf⟩

theorem endpointCircleWeightLp_apply (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (n : ℕ) :
    endpointCircleWeightLp r hrHalf n =
      Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (-r)) := rfl

/-- Every weighted `lp 2` input has absolutely summable physical
coefficients when `r>1/2`. -/
theorem summable_endpointCirclePhysicalCoeff_norm
    (r : ℝ) (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) :
    Summable (fun n : ℕ => ‖physicalCoeff r y n‖) := by
  have h22 : (ENNReal.toReal (2 : ENNReal)).HolderConjugate
      (ENNReal.toReal (2 : ENNReal)) := by
    change (2 : ℝ).HolderConjugate 2
    constructor <;> norm_num
  have hprod := lp.summable_mul h22 (endpointCircleWeightLp r hrHalf) y
  simpa [physicalCoeff, endpointCircleWeightLp_apply, norm_mul] using hprod

#assert_trust kernel endpointCircleWeightLp_apply
#assert_trust kernel summable_endpointCirclePhysicalCoeff_norm
#print axioms summable_endpointCirclePhysicalCoeff_norm

end NLA.Proofs.SP14
