import ProofProject.AnalyticSector

/-!
# An analytic majorant for squared norms

If `q` is zero-free, the maximum modulus principle applied to `a*f²/q`
propagates `a*|f|² ≤ |q|` from the circle to the disk. This gives the
majorization needed here without an additional Poisson integral theorem.
-/

noncomputable section

namespace ProofProject

open Metric Set

theorem analytic_sq_norm_majorant {f q : ℂ → ℂ} {a : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall 0 1))
    (hq : DifferentiableOn ℂ q (closedBall 0 1))
    (hqnz : ∀ z : ℂ, ‖z‖ ≤ 1 → q z ≠ 0) (ha : 0 ≤ a)
    (hbd : ∀ z : ℂ, ‖z‖ = 1 → a * ‖f z‖ ^ 2 ≤ ‖q z‖)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : a * ‖f z‖ ^ 2 ≤ ‖q z‖ := by
  let g : ℂ → ℂ := fun w => (a : ℂ) * (f w) ^ 2 / q w
  have hg : DifferentiableOn ℂ g (closedBall 0 1) :=
    ((hf.pow 2).const_mul (a : ℂ)).div hq
      (fun w hw => hqnz w (by simpa only [mem_closedBall, dist_zero_right] using hw))
  have hgn (w : ℂ) : ‖g w‖ = a * ‖f w‖ ^ 2 / ‖q w‖ := by
    simp only [g, norm_div, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ha]
  have hb : ∀ w ∈ frontier (ball (0 : ℂ) 1), ‖g w‖ ≤ 1 := by
    intro w hw
    have hw' : ‖w‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using frontier_ball_subset_sphere hw
    rw [hgn]
    exact (div_le_one (norm_pos_iff.mpr (hqnz w hw'.le))).mpr (hbd w hw')
  have hz' : z ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hm := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hg.diffContOnCl_ball subset_rfl) hb hz'
  rw [hgn] at hm
  exact (div_le_one (norm_pos_iff.mpr (hqnz z hz))).mp hm

end ProofProject
