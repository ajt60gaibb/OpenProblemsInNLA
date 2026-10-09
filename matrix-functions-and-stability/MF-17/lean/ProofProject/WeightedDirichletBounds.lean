import ProofProject.PowerIntegralBounds
import ProofProject.DirichletKernel

/-!
# Local weighted Dirichlet integral bounds

On `[0,1]`, the positive-power weight gives an upper bound of order `n^(1-α)`,
while the singular-power weight gives a lower bound of order `n^(1+α)`. These
are explicit scalar estimates for the weighted Dirichlet kernel.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

/-- Multiplying an integrable power by the squared norm of the finite
trigonometric polynomial preserves interval integrability. -/
lemma intervalIntegrable_weighted_dirichlet {β : ℝ} (hβ : -1 < β)
    (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => θ ^ β * ‖dirichletKernel n θ‖ ^ 2) volume a b :=
  (intervalIntegral.intervalIntegrable_rpow' hβ).mul_continuousOn
    (((continuous_dirichletKernel n).norm.pow 2).continuousOn)

/-- On the positive principal arc, the inverse-angle kernel bound supplies
the denominator's tail majorant. -/
lemma weighted_dirichlet_tail_pointwise (α : ℝ) (n : ℕ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    θ ^ α * ‖dirichletKernel n θ‖ ^ 2 ≤ Real.pi ^ 2 * θ ^ (α - 2) := by
  have hnorm : ‖dirichletKernel n θ‖ ≤ Real.pi / θ := by
    simpa only [abs_of_pos hθ0] using norm_dirichletKernel_le_pi_div
      (show 0 < |θ| by simpa [abs_of_pos hθ0])
      (show |θ| ≤ Real.pi by rw [abs_of_pos hθ0]; linarith [Real.pi_gt_three])
  calc
    _ ≤ θ ^ α * (Real.pi / θ) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
        (Real.rpow_nonneg hθ0.le _)
    _ = _ := by
      rw [Real.rpow_sub hθ0, Real.rpow_two, div_pow]
      ring

/-- The precise local upper estimate used for the reciprocal analytic weight. -/
theorem weighted_dirichlet_denominator_upper {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (hn : 1 ≤ n) :
    (∫ θ : ℝ in (0 : ℝ)..1, θ ^ α * ‖dirichletKernel n θ‖ ^ 2) ≤
      (1 / (1 + α) + Real.pi ^ 2 / (1 - α)) * (n : ℝ) ^ (1 - α) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hcutpos : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnpos
  have hcut : 1 / (n : ℝ) ≤ 1 := (div_le_one hnpos).mpr hnr
  have hint (a b : ℝ) := intervalIntegrable_weighted_dirichlet (by linarith : -1 < α) n a b
  have hsmall : (∫ θ : ℝ in (0 : ℝ)..(1 / (n : ℝ)),
      θ ^ α * ‖dirichletKernel n θ‖ ^ 2) ≤
        (n : ℝ) ^ 2 * (∫ θ : ℝ in (0 : ℝ)..(1 / (n : ℝ)), θ ^ α) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hcutpos.le (hint _ _)
      ((intervalIntegrable_positive_power hα0 _).const_mul _)
    intro θ hθ
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (norm_dirichletKernel_le n θ) 2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hθ.1 α)
  have htail : (∫ θ : ℝ in (1 / (n : ℝ))..1,
      θ ^ α * ‖dirichletKernel n θ‖ ^ 2) ≤
        Real.pi ^ 2 * (∫ θ : ℝ in (1 / (n : ℝ))..1, θ ^ (α - 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hcut (hint _ _)
      ((intervalIntegrable_power_tail α hnpos).const_mul _)
    intro θ hθ
    exact weighted_dirichlet_tail_pointwise α n (hcutpos.trans_le hθ.1) hθ.2
  rw [dirichlet_denominator_small_integral hα0 hnpos] at hsmall
  rw [dirichlet_denominator_tail_integral hα1 hnpos] at htail
  have hdrop : ((n : ℝ) ^ (1 - α) - 1) / (1 - α) ≤
      (n : ℝ) ^ (1 - α) / (1 - α) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  calc
    _ = (∫ θ : ℝ in (0 : ℝ)..(1 / (n : ℝ)), θ ^ α * ‖dirichletKernel n θ‖ ^ 2) +
        (∫ θ : ℝ in (1 / (n : ℝ))..1, θ ^ α * ‖dirichletKernel n θ‖ ^ 2) :=
      (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
    _ ≤ (n : ℝ) ^ (1 - α) / (1 + α) +
        Real.pi ^ 2 * (((n : ℝ) ^ (1 - α) - 1) / (1 - α)) := add_le_add hsmall htail
    _ ≤ (n : ℝ) ^ (1 - α) / (1 + α) +
        Real.pi ^ 2 * ((n : ℝ) ^ (1 - α) / (1 - α)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hdrop (sq_nonneg _)) _
    _ = _ := by ring

/-- The central arc supplies the singular-weight lower estimate. -/
theorem weighted_dirichlet_numerator_lower {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (1 + α) / (4 * (1 - α)) ≤
      ∫ θ : ℝ in (0 : ℝ)..1, θ ^ (-α) * ‖dirichletKernel n θ‖ ^ 2 := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hcutpos : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnpos
  have hcut : 1 / (n : ℝ) ≤ 1 := (div_le_one hnpos).mpr hnr
  have hint (a b : ℝ) := intervalIntegrable_weighted_dirichlet (by linarith : -1 < -α) n a b
  have hsmall : ((n : ℝ) ^ 2 / 4) *
      (∫ θ : ℝ in (0 : ℝ)..(1 / (n : ℝ)), θ ^ (-α)) ≤
        ∫ θ : ℝ in (0 : ℝ)..(1 / (n : ℝ)), θ ^ (-α) * ‖dirichletKernel n θ‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hcutpos.le
      ((intervalIntegrable_singular_power hα1 _).const_mul _) (hint _ _)
    intro θ hθ
    have hsq := norm_sq_dirichletKernel_lower hn
      (show |θ| ≤ 1 / (n : ℝ) by simpa only [abs_of_nonneg hθ.1] using hθ.2)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hθ.1 (-α))
  have hexact : ((n : ℝ) ^ 2 / 4) *
      (∫ θ : ℝ in (0 : ℝ)..(1 / (n : ℝ)), θ ^ (-α)) =
        (n : ℝ) ^ (1 + α) / (4 * (1 - α)) := by
    calc
      _ = ((n : ℝ) ^ 2 * (∫ θ : ℝ in (0 : ℝ)..(1 / (n : ℝ)), θ ^ (-α))) / 4 := by ring
      _ = _ := by
        rw [dirichlet_numerator_power_integral hα1 hnpos]
        field_simp [show 1 - α ≠ 0 by linarith]
  rw [hexact] at hsmall
  have htail : 0 ≤ ∫ θ : ℝ in (1 / (n : ℝ))..1,
      θ ^ (-α) * ‖dirichletKernel n θ‖ ^ 2 := by
    apply intervalIntegral.integral_nonneg hcut
    intro θ hθ
    exact mul_nonneg (Real.rpow_nonneg (hcutpos.le.trans hθ.1) _) (sq_nonneg _)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 (1 / (n : ℝ)))
    (hint (1 / (n : ℝ)) 1)]
  linarith

end ProofProject
