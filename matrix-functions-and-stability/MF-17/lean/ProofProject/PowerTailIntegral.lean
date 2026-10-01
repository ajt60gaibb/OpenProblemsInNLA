import ProofProject.SemigroupKernelOperator
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The absolute power-tail remainder bound

The source primitive leaves a remainder dominated by `u^(-5/4)` above a
positive lower support threshold. The improper integral converges and supplies
the exact factor four; the source coefficient `3A/2` then gives `6A`.
-/

noncomputable section

open MeasureTheory Set

namespace ProofProject

theorem integrableOn_rpow_neg_five_quarters {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun u : ℝ => u ^ (-5 / 4 : ℝ)) (Ioi δ) :=
  integrableOn_Ioi_rpow_of_lt (by norm_num) hδ

theorem integral_rpow_neg_five_quarters {δ : ℝ} (hδ : 0 < δ) :
    (∫ u : ℝ in Ioi δ, u ^ (-5 / 4 : ℝ)) = 4 * δ ^ (-1 / 4 : ℝ) := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-5 / 4 : ℝ) < -1) hδ]
  norm_num
  ring

/-- The value at the support endpoint is irrelevant to the integral. Scalar
integrability is an explicit premise, independently of the estimate. -/
theorem integral_norm_le_power_tail {δ C : ℝ} (hδ : 0 < δ) {f : ℝ → ℂ}
    (hf : Integrable f) (hsupp : ∀ u < δ, f u = 0)
    (hbound : ∀ u > 0, ‖f u‖ ≤ C * u ^ (-5 / 4 : ℝ)) :
    (∫ u : ℝ, ‖f u‖) ≤ 4 * C * δ ^ (-1 / 4 : ℝ) := by
  have hrestrict : (∫ u : ℝ, ‖f u‖) = ∫ u : ℝ in Ioi δ, ‖f u‖ := by
    rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      dsimp only
      by_cases hu : u ∈ Ici δ
      · rw [indicator_of_mem hu]
      · rw [indicator_of_notMem hu, hsupp u (lt_of_not_ge hu), norm_zero]
  rw [hrestrict]
  calc
    _ ≤ ∫ u : ℝ in Ioi δ, C * u ^ (-5 / 4 : ℝ) :=
      setIntegral_mono_on hf.norm.integrableOn
        ((integrableOn_rpow_neg_five_quarters hδ).const_mul C) measurableSet_Ioi
        (fun u hu => hbound u (hδ.trans hu))
    _ = _ := by rw [integral_const_mul, integral_rpow_neg_five_quarters hδ]; ring

/-- The exact source remainder constant after inserting `3A/2`. -/
theorem integral_norm_le_source_power_tail {δ A : ℝ} (hδ : 0 < δ) {f : ℝ → ℂ}
    (hf : Integrable f) (hsupp : ∀ u < δ, f u = 0)
    (hbound : ∀ u > 0, ‖f u‖ ≤ (3 / 2 : ℝ) * A * u ^ (-5 / 4 : ℝ)) :
    (∫ u : ℝ, ‖f u‖) ≤ 6 * A * δ ^ (-1 / 4 : ℝ) := by
  convert integral_norm_le_power_tail hδ hf hsupp hbound using 1 <;> ring

namespace BoundedSemigroup

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Absolute integration of the remainder costs exactly the original
semigroup bound and the power-tail factor four. -/
theorem kernelOperator_norm_le_power_tail (S : BoundedSemigroup M H)
    {δ C : ℝ} (hδ : 0 < δ) {f : ℝ → ℂ} (hf : Integrable f)
    (hsupp : ∀ u < δ, f u = 0)
    (hbound : ∀ u > 0, ‖f u‖ ≤ C * u ^ (-5 / 4 : ℝ)) :
    ‖S.kernelOperator f hf‖ ≤ 4 * M * C * δ ^ (-1 / 4 : ℝ) := by
  apply (S.kernelOperator_norm_le f hf).trans
  have h := mul_le_mul_of_nonneg_left (integral_norm_le_power_tail hδ hf hsupp hbound)
    S.bound_nonneg
  convert h using 1 <;> ring

end BoundedSemigroup

end ProofProject
