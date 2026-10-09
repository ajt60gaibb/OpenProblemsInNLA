import ProofProject.RationalPhaseApproximation
import ProofProject.DiskSector
import ProofProject.AnalyticSector

/-! The actual analytic sector function obtained from the outer phase. -/

noncomputable section

namespace ProofProject

open Metric

/-- Multiplying the phase approximation by `h²` gives a disk centered at
the actual positive boundary weight. -/
lemma phase_error_mul_sq {a b : ℂ} {ρ : ℝ} (hb : b ≠ 0)
    (herr : ‖starRingEnd ℂ b / b - a‖ ≤ ρ) :
    ‖a * b ^ 2 - (‖b‖ ^ 2 : ℝ)‖ ≤ ρ * ‖b‖ ^ 2 := by
  have hn : ((‖b‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ b * b := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  have he : a * b ^ 2 - (‖b‖ ^ 2 : ℝ) = (a - starRingEnd ℂ b / b) * b ^ 2 := by
    rw [hn]
    field_simp
  rw [he, norm_mul, norm_pow, norm_sub_rev]
  exact mul_le_mul_of_nonneg_right herr (sq_nonneg _)

/-- The weighted projection bound supplies an actual analytic function in
the exact sector, with a strictly positive real part on the closed disk. -/
theorem exists_outerSectorFunction {h : Polynomial ℂ} {K : ℝ}
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0)
    (hproj : HasPolynomialCircleProjectionBound h K) (hK : 1 < K) :
    ∃ q : ℂ → ℂ, ∃ r : ℝ, 1 < r ∧
      DifferentiableOn ℂ q (closedBall 0 r) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → 0 < (q z).re ∧
        |(q z).im| ≤ (K * Real.sqrt (1 - K⁻¹ ^ 2)) * (q z).re) ∧
      (∀ z : ℂ, ‖z‖ = 1 →
        ‖q z - (‖h.eval z‖ ^ 2 : ℝ)‖ ≤ Real.sqrt (1 - K⁻¹ ^ 2) * ‖h.eval z‖ ^ 2) := by
  obtain ⟨f, r, hr, hf, herr⟩ := exists_polynomialPhase_analytic_approximation hh hproj hK
  let q : ℂ → ℂ := fun z => f z * (h.eval z) ^ 2
  have hf' : DifferentiableOn ℂ f (closedBall 0 1) :=
    hf.mono (closedBall_subset_closedBall hr.le)
  have hq : DifferentiableOn ℂ q (closedBall 0 1) :=
    hf'.mul (h.differentiable.differentiableOn.pow 2)
  have hdisk (z : ℂ) (hz : ‖z‖ = 1) :
      ‖q z - (‖h.eval z‖ ^ 2 : ℝ)‖ ≤ Real.sqrt (1 - K⁻¹ ^ 2) * ‖h.eval z‖ ^ 2 :=
    phase_error_mul_sq (hh z hz.le) (herr z hz)
  have hsector (z : ℂ) (hz : ‖z‖ = 1) :
      0 < (q z).re ∧ |(q z).im| ≤ (K * Real.sqrt (1 - K⁻¹ ^ 2)) * (q z).re := by
    have hw : 0 < ‖h.eval z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (hh z hz.le))
    exact (diskSector_growthParameter hK hw (hdisk z hz)).2
  refine ⟨q, r, hr, hf.mul (h.differentiable.differentiableOn.pow 2), ?_, hdisk⟩
  intro z hz
  exact ⟨analytic_re_pos_of_unit_circle hq (fun w hw => (hsector w hw).1) hz,
    analytic_sector_of_unit_circle hq (fun w hw => (hsector w hw).2) hz⟩

end ProofProject
