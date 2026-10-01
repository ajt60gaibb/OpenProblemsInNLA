import Mathlib

/-!
# Propagating real-part and sector bounds from the unit circle

The maximum modulus principle applied to an exponential preserves real
linear inequalities on an analytic function. A positive circle minimum
also gives strict positivity throughout the closed disk.
-/

noncomputable section

namespace ProofProject

open Metric Set

lemma analytic_re_le_of_unit_circle {f : ℂ → ℂ} {a : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall 0 1))
    (hbd : ∀ z : ℂ, ‖z‖ = 1 → (f z).re ≤ a)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : (f z).re ≤ a := by
  apply Real.exp_le_exp.mp
  have hm := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hf.cexp.diffContOnCl_ball subset_rfl) (C := Real.exp a)
  have hb : ∀ w ∈ frontier (ball (0 : ℂ) 1), ‖Complex.exp (f w)‖ ≤ Real.exp a := by
    intro w hw
    have hw' : ‖w‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using frontier_ball_subset_sphere hw
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hbd w hw')
  have hz' : z ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    simpa only [mem_closedBall, dist_zero_right] using hz
  simpa only [Complex.norm_exp] using hm hb hz'

lemma analytic_re_ge_of_unit_circle {f : ℂ → ℂ} {a : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall 0 1))
    (hbd : ∀ z : ℂ, ‖z‖ = 1 → a ≤ (f z).re)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : a ≤ (f z).re := by
  have h := analytic_re_le_of_unit_circle hf.neg
    (a := -a) (fun w hw => by simpa using neg_le_neg (hbd w hw)) hz
  simpa using h

lemma analytic_re_pos_of_unit_circle {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 1))
    (hbd : ∀ z : ℂ, ‖z‖ = 1 → 0 < (f z).re)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : 0 < (f z).re := by
  have hc : ContinuousOn (fun w => (f w).re) (sphere (0 : ℂ) 1) :=
    Complex.continuous_re.comp_continuousOn
      (hf.continuousOn.mono sphere_subset_closedBall)
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMinOn
    (show (sphere (0 : ℂ) 1).Nonempty from ⟨1, by simp⟩) hc
  have hw' : ‖w‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hw
  exact (hbd w hw').trans_le (analytic_re_ge_of_unit_circle hf
    (fun v hv => hmin (by simpa only [mem_sphere, dist_zero_right] using hv)) hz)

/-- A sector is the intersection of two real half-planes, so its exact slope
is preserved without introducing a complex argument function. -/
lemma analytic_sector_of_unit_circle {f : ℂ → ℂ} {T : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall 0 1))
    (hbd : ∀ z : ℂ, ‖z‖ = 1 → |(f z).im| ≤ T * (f z).re)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : |(f z).im| ≤ T * (f z).re := by
  have hp := analytic_re_ge_of_unit_circle (hf.const_mul ((T : ℂ) + Complex.I))
    (a := 0) (fun w hw => by
      have h := (abs_le.mp (hbd w hw)).2
      simp only [Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      linarith) hz
  have hn := analytic_re_ge_of_unit_circle (hf.const_mul ((T : ℂ) - Complex.I))
    (a := 0) (fun w hw => by
      have h := (abs_le.mp (hbd w hw)).1
      simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      linarith) hz
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im] at hp hn
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ProofProject
