import NLA.Proofs.SP14.EndpointCircleCoeffSummable
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
The continuous two-sided circle series of the canonical endpoint extension
at `1/2 < r < 1`. Its frozen Fourier-integral identities are a later gate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private theorem endpointCirclePositive_term_norm (r : ℝ)
    (y : SobolevCoeff r) (n : ℕ) (z : Circle) :
    ‖physicalCoeff r y n * (z : ℂ) ^ n‖ = ‖physicalCoeff r y n‖ := by
  simp [Circle.norm_coe]

private theorem endpointCircleNegative_term_norm (r : ℝ)
    (v : SobolevCoeff r) (n : ℕ) (z : Circle) :
    ‖physicalCoeff r v n * (z : ℂ) ^ (-((n + 1 : ℕ) : ℤ))‖ =
      ‖physicalCoeff r v n‖ := by
  simp [norm_zpow, Circle.norm_coe]

/-- The nonnegative Fourier series, with zero mode at `n=0`. -/
noncomputable def endpointCirclePositiveSeries (r : ℝ)
    (y : SobolevCoeff r) (z : Circle) : ℂ :=
  ∑' n : ℕ, physicalCoeff r y n * (z : ℂ) ^ n

/-- The strictly negative Fourier series, starting at mode `-1`. -/
noncomputable def endpointCircleNegativeSeries (r : ℝ)
    (v : SobolevCoeff r) (z : Circle) : ℂ :=
  ∑' n : ℕ, physicalCoeff r v n * (z : ℂ) ^ (-((n + 1 : ℕ) : ℤ))

theorem summable_endpointCirclePositive_terms (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) (z : Circle) :
    Summable (fun n : ℕ => physicalCoeff r y n * (z : ℂ) ^ n) := by
  apply Summable.of_norm_bounded (summable_endpointCirclePhysicalCoeff_norm r hrHalf y)
  intro n
  exact (endpointCirclePositive_term_norm r y n z).le

theorem summable_endpointCircleNegative_terms (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (v : SobolevCoeff r) (z : Circle) :
    Summable (fun n : ℕ =>
      physicalCoeff r v n * (z : ℂ) ^ (-((n + 1 : ℕ) : ℤ))) := by
  apply Summable.of_norm_bounded (summable_endpointCirclePhysicalCoeff_norm r hrHalf v)
  intro n
  exact (endpointCircleNegative_term_norm r v n z).le

theorem continuous_endpointCirclePositiveSeries (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) :
    Continuous (endpointCirclePositiveSeries r y) := by
  unfold endpointCirclePositiveSeries
  apply continuous_tsum
  · intro n
    exact continuous_const.mul (continuous_subtype_val.pow n)
  · exact summable_endpointCirclePhysicalCoeff_norm r hrHalf y
  · intro n z
    exact (endpointCirclePositive_term_norm r y n z).le

theorem continuous_endpointCircleNegativeSeries (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (v : SobolevCoeff r) :
    Continuous (endpointCircleNegativeSeries r v) := by
  unfold endpointCircleNegativeSeries
  apply continuous_tsum
  · intro n
    have hp : Continuous (fun z : Circle => (z : Circle) ^ (-((n + 1 : ℕ) : ℤ))) :=
      continuous_zpow _
    have hcoe : Continuous (fun z : Circle => (z : ℂ) ^ (-((n + 1 : ℕ) : ℤ))) := by
      apply (continuous_subtype_val.comp hp).congr
      intro z
      exact Circle.coe_zpow z _
    exact continuous_const.mul hcoe
  · exact summable_endpointCirclePhysicalCoeff_norm r hrHalf v
  · intro n z
    exact (endpointCircleNegative_term_norm r v n z).le

/-- The circle function with the actual negative Fourier operator as its
negative block. -/
noncomputable def endpointCircleRealization (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (z : Circle) : ℂ :=
  endpointCirclePositiveSeries r y z +
    endpointCircleNegativeSeries r
      (endpointNegativeOperator r (by linarith) hr1 y) z

theorem continuous_endpointCircleRealization (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) :
    Continuous (endpointCircleRealization r hrHalf hr1 y) := by
  exact (continuous_endpointCirclePositiveSeries r hrHalf y).add
    (continuous_endpointCircleNegativeSeries r hrHalf
      (endpointNegativeOperator r (by linarith) hr1 y))

#assert_trust kernel summable_endpointCirclePositive_terms
#assert_trust kernel summable_endpointCircleNegative_terms
#assert_trust kernel continuous_endpointCircleRealization
#print axioms continuous_endpointCircleRealization

end NLA.Proofs.SP14
