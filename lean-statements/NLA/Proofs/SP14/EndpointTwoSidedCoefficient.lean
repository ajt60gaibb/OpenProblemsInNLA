import NLA.Proofs.SP14.EndpointNegativeOperator

/-!
The canonical endpoint extension as a two-block weighted coefficient map.
The `true` block holds the nonnegative modes, including zero; the `false`
block holds the negative modes indexed by `-(t+1)`.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The two-sided coefficient carrier with its genuine orthogonal-sum norm. -/
noncomputable abbrev TwoSidedCoeff (r : ℝ) :=
  lp (fun _ : Bool => SobolevCoeff r) 2

private noncomputable def endpointTwoSidedCoeff (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (y : SobolevCoeff r) : TwoSidedCoeff r :=
  ⟨fun b => if b then y else endpointNegativeOperator r hr hr1 y, Memℓp.all _⟩

private theorem endpointTwoSidedCoeff_norm_sq (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (y : SobolevCoeff r) :
    ‖endpointTwoSidedCoeff r hr hr1 y‖ ^ 2 =
      ‖y‖ ^ 2 + ‖endpointNegativeOperator r hr hr1 y‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ENNReal).toReal)
    (endpointTwoSidedCoeff r hr hr1 y)
  calc
    ‖endpointTwoSidedCoeff r hr hr1 y‖ ^ 2 =
        ‖endpointTwoSidedCoeff r hr hr1 y‖ ^ (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    _ = ∑' b : Bool, ‖endpointTwoSidedCoeff r hr hr1 y b‖ ^ 2 := by
      simpa using h
    _ = ‖y‖ ^ 2 + ‖endpointNegativeOperator r hr hr1 y‖ ^ 2 := by
      simp [tsum_fintype, endpointTwoSidedCoeff]

private theorem endpointTwoSidedCoeff_norm_le (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (y : SobolevCoeff r) :
    ‖endpointTwoSidedCoeff r hr hr1 y‖ ≤
      Real.sqrt (1 + endpointSchurConstant r ^ 2) * ‖y‖ := by
  have hC : 0 ≤ endpointSchurConstant r := by
    unfold endpointSchurConstant
    have : 0 < 1 - r := by linarith
    positivity
  have hT : ‖endpointNegativeOperator r hr hr1 y‖ ≤
      endpointSchurConstant r * ‖y‖ :=
    (endpointNegativeOperator r hr hr1).le_opNorm y |>.trans
      (mul_le_mul_of_nonneg_right (endpointNegativeOperator_norm_le r hr hr1)
        (norm_nonneg y))
  have hsq := endpointTwoSidedCoeff_norm_sq r hr hr1 y
  have hsqrt : 0 ≤ Real.sqrt (1 + endpointSchurConstant r ^ 2) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (1 + endpointSchurConstant r ^ 2)) ^ 2 =
      1 + endpointSchurConstant r ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hTsq : ‖endpointNegativeOperator r hr hr1 y‖ ^ 2 ≤
      (endpointSchurConstant r * ‖y‖) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT)
      (add_nonneg (mul_nonneg hC (norm_nonneg y))
        (norm_nonneg (endpointNegativeOperator r hr hr1 y)))]
  have hbound_sq : ‖endpointTwoSidedCoeff r hr hr1 y‖ ^ 2 ≤
      (Real.sqrt (1 + endpointSchurConstant r ^ 2) * ‖y‖) ^ 2 := by
    rw [hsq, mul_pow, hsqrt_sq]
    nlinarith
  nlinarith [norm_nonneg (endpointTwoSidedCoeff r hr hr1 y),
    mul_nonneg hsqrt (norm_nonneg y)]

private noncomputable def endpointTwoSidedCoeffLinear (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) : SobolevCoeff r →ₗ[ℂ] TwoSidedCoeff r where
  toFun := endpointTwoSidedCoeff r hr hr1
  map_add' y z := by
    apply lp.ext
    funext b
    cases b
    · change endpointNegativeOperator r hr hr1 (y + z) =
        endpointNegativeOperator r hr hr1 y + endpointNegativeOperator r hr hr1 z
      exact map_add _ _ _
    · change y + z = y + z
      rfl
  map_smul' c y := by
    apply lp.ext
    funext b
    cases b
    · change endpointNegativeOperator r hr hr1 (c • y) =
        c • endpointNegativeOperator r hr hr1 y
      exact map_smul _ _ _
    · change c • y = c • y
      rfl

/-- The actual bounded two-sided coefficient extension. -/
noncomputable def endpointTwoSidedCoeffOperator (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) : SobolevCoeff r →L[ℂ] TwoSidedCoeff r :=
  (endpointTwoSidedCoeffLinear r hr hr1).mkContinuous
    (Real.sqrt (1 + endpointSchurConstant r ^ 2))
    (endpointTwoSidedCoeff_norm_le r hr hr1)

theorem endpointTwoSidedCoeffOperator_true (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (y : SobolevCoeff r) :
    endpointTwoSidedCoeffOperator r hr hr1 y true = y := rfl

theorem endpointTwoSidedCoeffOperator_false (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (y : SobolevCoeff r) :
    endpointTwoSidedCoeffOperator r hr hr1 y false =
      endpointNegativeOperator r hr hr1 y := rfl

theorem endpointTwoSidedCoeffOperator_norm_sq (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (y : SobolevCoeff r) :
    ‖endpointTwoSidedCoeffOperator r hr hr1 y‖ ^ 2 =
      ‖y‖ ^ 2 + ‖endpointNegativeOperator r hr hr1 y‖ ^ 2 :=
  endpointTwoSidedCoeff_norm_sq r hr hr1 y

theorem endpointTwoSidedCoeffOperator_apply_norm_le (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (y : SobolevCoeff r) :
    ‖endpointTwoSidedCoeffOperator r hr hr1 y‖ ≤
      Real.sqrt (1 + endpointSchurConstant r ^ 2) * ‖y‖ :=
  endpointTwoSidedCoeff_norm_le r hr hr1 y

theorem endpointTwoSidedCoeffOperator_norm_le (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) :
    ‖endpointTwoSidedCoeffOperator r hr hr1‖ ≤
      Real.sqrt (1 + endpointSchurConstant r ^ 2) := by
  have hC : 0 ≤ Real.sqrt (1 + endpointSchurConstant r ^ 2) := Real.sqrt_nonneg _
  exact LinearMap.mkContinuous_norm_le _ hC (endpointTwoSidedCoeff_norm_le r hr hr1)

#assert_trust kernel endpointTwoSidedCoeffOperator_true
#assert_trust kernel endpointTwoSidedCoeffOperator_false
#assert_trust kernel endpointTwoSidedCoeffOperator_norm_sq
#assert_trust kernel endpointTwoSidedCoeffOperator_apply_norm_le
#assert_trust kernel endpointTwoSidedCoeffOperator_norm_le
#print axioms endpointTwoSidedCoeffOperator_norm_le

end NLA.Proofs.SP14
