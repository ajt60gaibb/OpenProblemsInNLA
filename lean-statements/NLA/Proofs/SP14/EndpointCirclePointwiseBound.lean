import NLA.Proofs.SP14.EndpointCircleSeries

/-!
The exact pointwise bound for the actual two-sided endpoint circle series.
The subtraction identity makes the same bound available for limits in the
weighted input norm; endpoint vanishing is a later gate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private theorem endpointPhysicalCoeff_tsum_norm_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) :
    (∑' n : ℕ, ‖physicalCoeff r y n‖) ≤
      ‖endpointCircleWeightLp r hrHalf‖ * ‖y‖ := by
  have h22 : (ENNReal.toReal (2 : ENNReal)).HolderConjugate
      (ENNReal.toReal (2 : ENNReal)) := by
    change (2 : ℝ).HolderConjugate 2
    constructor <;> norm_num
  have h := lp.tsum_mul_le_mul_norm' h22
    (endpointCircleWeightLp r hrHalf) y
  simpa [physicalCoeff, endpointCircleWeightLp_apply, norm_mul] using h

private theorem endpointCirclePositiveSeries_norm_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) (z : Circle) :
    ‖endpointCirclePositiveSeries r y z‖ ≤
      ‖endpointCircleWeightLp r hrHalf‖ * ‖y‖ := by
  have habs : Summable (fun n : ℕ =>
      ‖physicalCoeff r y n * (z : ℂ) ^ n‖) := by
    simpa [Circle.norm_coe] using
      (summable_endpointCirclePhysicalCoeff_norm r hrHalf y)
  calc
    ‖endpointCirclePositiveSeries r y z‖ ≤
        ∑' n : ℕ, ‖physicalCoeff r y n * (z : ℂ) ^ n‖ := by
      exact norm_tsum_le_tsum_norm habs
    _ = ∑' n : ℕ, ‖physicalCoeff r y n‖ := by
      congr 1
      funext n
      simp [Circle.norm_coe]
    _ ≤ ‖endpointCircleWeightLp r hrHalf‖ * ‖y‖ :=
      endpointPhysicalCoeff_tsum_norm_le r hrHalf y

private theorem endpointCircleNegativeSeries_norm_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (v : SobolevCoeff r) (z : Circle) :
    ‖endpointCircleNegativeSeries r v z‖ ≤
      ‖endpointCircleWeightLp r hrHalf‖ * ‖v‖ := by
  have habs : Summable (fun n : ℕ =>
      ‖physicalCoeff r v n * (z : ℂ) ^ (-((n + 1 : ℕ) : ℤ))‖) := by
    simpa [norm_zpow, Circle.norm_coe] using
      (summable_endpointCirclePhysicalCoeff_norm r hrHalf v)
  calc
    ‖endpointCircleNegativeSeries r v z‖ ≤
        ∑' n : ℕ,
          ‖physicalCoeff r v n * (z : ℂ) ^ (-((n + 1 : ℕ) : ℤ))‖ := by
      exact norm_tsum_le_tsum_norm habs
    _ = ∑' n : ℕ, ‖physicalCoeff r v n‖ := by
      congr 1
      funext n
      simp [norm_zpow, Circle.norm_coe]
    _ ≤ ‖endpointCircleWeightLp r hrHalf‖ * ‖v‖ :=
      endpointPhysicalCoeff_tsum_norm_le r hrHalf v

/-- Exact input-norm control of the actual two-sided circle realization. -/
theorem endpointCircleRealization_pointwise_norm_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (z : Circle) :
    ‖endpointCircleRealization r hrHalf hr1 y z‖ ≤
      ‖endpointCircleWeightLp r hrHalf‖ *
        (1 + endpointSchurConstant r) * ‖y‖ := by
  have hr : 0 < r := by linarith
  let V := endpointNegativeOperator r hr hr1 y
  have hV : ‖V‖ ≤ endpointSchurConstant r * ‖y‖ :=
    (endpointNegativeOperator r hr hr1).le_opNorm y |>.trans
      (mul_le_mul_of_nonneg_right (endpointNegativeOperator_norm_le r hr hr1)
        (norm_nonneg y))
  have hW : 0 ≤ ‖endpointCircleWeightLp r hrHalf‖ := norm_nonneg _
  calc
    ‖endpointCircleRealization r hrHalf hr1 y z‖ ≤
        ‖endpointCirclePositiveSeries r y z‖ +
          ‖endpointCircleNegativeSeries r V z‖ := by
      exact norm_add_le _ _
    _ ≤ ‖endpointCircleWeightLp r hrHalf‖ * ‖y‖ +
          ‖endpointCircleWeightLp r hrHalf‖ * ‖V‖ := by
      exact add_le_add
        (endpointCirclePositiveSeries_norm_le r hrHalf y z)
        (endpointCircleNegativeSeries_norm_le r hrHalf V z)
    _ ≤ ‖endpointCircleWeightLp r hrHalf‖ * ‖y‖ +
          ‖endpointCircleWeightLp r hrHalf‖ *
            (endpointSchurConstant r * ‖y‖) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hV hW) _
    _ = _ := by ring

private theorem endpointCirclePositiveSeries_sub (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y x : SobolevCoeff r) (z : Circle) :
    endpointCirclePositiveSeries r (y - x) z =
      endpointCirclePositiveSeries r y z - endpointCirclePositiveSeries r x z := by
  unfold endpointCirclePositiveSeries
  calc
    (∑' n : ℕ, physicalCoeff r (y - x) n * (z : ℂ) ^ n) =
        ∑' n : ℕ,
          (physicalCoeff r y n * (z : ℂ) ^ n -
            physicalCoeff r x n * (z : ℂ) ^ n) := by
      congr 1
      funext n
      simp only [physicalCoeff, lp.coeFn_sub, Pi.sub_apply]
      ring
    _ = _ := (summable_endpointCirclePositive_terms r hrHalf y z).tsum_sub
      (summable_endpointCirclePositive_terms r hrHalf x z)

private theorem endpointCircleNegativeSeries_sub (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (v w : SobolevCoeff r) (z : Circle) :
    endpointCircleNegativeSeries r (v - w) z =
      endpointCircleNegativeSeries r v z - endpointCircleNegativeSeries r w z := by
  unfold endpointCircleNegativeSeries
  calc
    (∑' n : ℕ,
      physicalCoeff r (v - w) n * (z : ℂ) ^ (-((n + 1 : ℕ) : ℤ))) =
        ∑' n : ℕ,
          (physicalCoeff r v n * (z : ℂ) ^ (-((n + 1 : ℕ) : ℤ)) -
            physicalCoeff r w n * (z : ℂ) ^ (-((n + 1 : ℕ) : ℤ))) := by
      congr 1
      funext n
      simp only [physicalCoeff, lp.coeFn_sub, Pi.sub_apply]
      ring
    _ = _ := (summable_endpointCircleNegative_terms r hrHalf v z).tsum_sub
      (summable_endpointCircleNegative_terms r hrHalf w z)

/-- Input subtraction is preserved by the actual two-sided circle series. -/
theorem endpointCircleRealization_sub (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y x : SobolevCoeff r) (z : Circle) :
    endpointCircleRealization r hrHalf hr1 (y - x) z =
      endpointCircleRealization r hrHalf hr1 y z -
        endpointCircleRealization r hrHalf hr1 x z := by
  unfold endpointCircleRealization
  rw [map_sub, endpointCirclePositiveSeries_sub r hrHalf y x z,
    endpointCircleNegativeSeries_sub r hrHalf]
  ring

/-- The exact pointwise difference bound used for weighted-input density. -/
theorem endpointCircleRealization_pointwise_sub_norm_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y x : SobolevCoeff r) (z : Circle) :
    ‖endpointCircleRealization r hrHalf hr1 y z -
        endpointCircleRealization r hrHalf hr1 x z‖ ≤
      ‖endpointCircleWeightLp r hrHalf‖ *
        (1 + endpointSchurConstant r) * ‖y - x‖ := by
  rw [← endpointCircleRealization_sub r hrHalf hr1 y x z]
  exact endpointCircleRealization_pointwise_norm_le r hrHalf hr1 (y - x) z

#assert_trust kernel endpointCircleRealization_pointwise_norm_le
#assert_trust kernel endpointCircleRealization_sub
#assert_trust kernel endpointCircleRealization_pointwise_sub_norm_le
#print axioms endpointCircleRealization_pointwise_sub_norm_le

end NLA.Proofs.SP14
