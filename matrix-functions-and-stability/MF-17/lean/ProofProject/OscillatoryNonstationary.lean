import ProofProject.OscillatoryIntegration
import ProofProject.OscillatoryFirstDerivative

/-!
# A first-derivative oscillatory bound for complex amplitudes

A real phase with monotone derivative bounded away from zero has an
oscillatory integral controlled by the amplitude and its total variation.
This is the estimate on the two nonstationary pieces in the second-derivative
test. No second-derivative lower bound or stationary-region splitting is
asserted here.
-/

noncomputable section

open MeasureTheory Set

namespace ProofProject

/-- Complex amplitudes obey the first-derivative bound with an absolute
constant, for either sign of the monotonicity of the phase derivative. -/
theorem norm_oscillatory_integral_le_first_derivative {a b δ C : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hC : 0 ≤ C)
    {A A' : ℝ → ℂ} {φ p p' : ℝ → ℝ}
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (p x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hA' : ContinuousOn A' (Icc a b)) (hp' : ContinuousOn p' (Icc a b))
    (hsep : ∀ x ∈ Icc a b, δ ≤ |p x|)
    (hbound : ∀ x ∈ Icc a b, ‖A x‖ ≤ C)
    (hsign : (∀ x ∈ Icc a b, 0 ≤ p' x) ∨ (∀ x ∈ Icc a b, p' x ≤ 0)) :
    ‖∫ x in a..b, A x * oscillatoryExponential φ x‖ ≤
      (4 * C + ∫ x in a..b, ‖A' x‖) / δ := by
  have hp0 (x : ℝ) (hx : x ∈ Icc a b) : p x ≠ 0 :=
    abs_pos.mp (hδ.trans_le (hsep x hx))
  have hAbs (x : ℝ) (hx : x ∈ Icc a b) : |p x| ≠ 0 := abs_ne_zero.mpr (hp0 x hx)
  have hAc : ContinuousOn A (Icc a b) := fun x hx => (hA x hx).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (Icc a b) := fun x hx => (hp x hx).continuousAt.continuousWithinAt
  have hvar : ContinuousOn (fun x => |p' x| / |p x| ^ 2) (Icc a b) :=
    hp'.abs.div (hpc.abs.pow 2) (fun x hx => pow_ne_zero _ (hAbs x hx))
  have hleft : ContinuousOn (fun x => ‖A' x‖ / |p x| +
      ‖A x‖ * |p' x| / |p x| ^ 2) (Icc a b) :=
    (hA'.norm.div hpc.abs hAbs).add ((hAc.norm.mul hp'.abs).div
      (hpc.abs.pow 2) (fun x hx => pow_ne_zero _ (hAbs x hx)))
  have hright : ContinuousOn (fun x => ‖A' x‖ / δ +
      C * (|p' x| / |p x| ^ 2)) (Icc a b) :=
    (hA'.norm.div_const δ).add (hvar.const_mul C)
  have hend (x : ℝ) (hx : x ∈ Icc a b) : ‖A x‖ / |p x| ≤ C / δ :=
    (div_le_div_of_nonneg_right (hbound x hx) (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left hC hδ (hsep x hx))
  have hrem : (∫ x in a..b, ‖A' x‖ / |p x| + ‖A x‖ * |p' x| / |p x| ^ 2) ≤
      (∫ x in a..b, ‖A' x‖) / δ + C * (2 / δ) := by
    calc
      _ ≤ ∫ x in a..b, ‖A' x‖ / δ + C * (|p' x| / |p x| ^ 2) := by
        apply intervalIntegral.integral_mono_on hab
          (hleft.intervalIntegrable_of_Icc hab) (hright.intervalIntegrable_of_Icc hab)
        intro x hx
        apply add_le_add (div_le_div_of_nonneg_left (norm_nonneg _) hδ (hsep x hx))
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (hbound x hx) (by positivity)
      _ = (∫ x in a..b, ‖A' x‖) / δ + C * (∫ x in a..b, |p' x| / |p x| ^ 2) := by
        rw [intervalIntegral.integral_add
          ((hA'.norm.div_const δ).intervalIntegrable_of_Icc hab)
          ((hvar.const_mul C).intervalIntegrable_of_Icc hab),
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (reciprocal_variation_le_two_div_of_continuousOn hab hδ hp hp' hsep hsign) hC)
  calc
    _ ≤ _ := norm_oscillatory_integral_le hab hA hφ hp hp0 hA' hp'
    _ ≤ C / δ + C / δ + ((∫ x in a..b, ‖A' x‖) / δ + C * (2 / δ)) :=
      add_le_add (add_le_add (hend b ⟨hab, le_rfl⟩) (hend a ⟨le_rfl, hab⟩)) hrem
    _ = _ := by ring

end ProofProject
