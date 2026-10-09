import ProofProject.MetricMargin

/-!
# The cubic separation scale eventually meets the scalar error budget

For a fixed replication number `r`, the metric margin at dimension `r*n`
decays only quadratically in `n`. Taking the separation parameter `n³` then
makes the unwanted early-coordinate exponential errors negligible.
-/

noncomputable section

open Filter Topology

namespace ProofProject

/-- An explicit positive coefficient in the inverse-square lower estimate for
the source's scalar error budget. -/
def separationBudgetConstant (M : ℝ) (r : ℕ) : ℝ :=
  ((M ^ 2 - 1) / (4 * M ^ 2 + 1)) / (12 * M ^ 2 * (r : ℝ) ^ 2)

lemma separationBudgetConstant_pos {M : ℝ} {r : ℕ} (hM : 1 < M) (hr : 0 < r) :
    0 < separationBudgetConstant M r := by
  have hnum : 0 < M ^ 2 - 1 := by nlinarith
  unfold separationBudgetConstant
  positivity

/-- At dimension `r*n`, the source budget is at least a fixed multiple of `n⁻²`. -/
lemma separationBudget_lower {M : ℝ} {r n : ℕ}
    (hM : 1 < M) (hr : 0 < r) (hn : 0 < n) :
    separationBudgetConstant M r / (n : ℝ) ^ 2 ≤
      metricGamma M (r * n) / (12 * M ^ 2) := by
  have hM0 : M ≠ 0 := by linarith
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hgamma := metricGamma_lower hM (Nat.mul_pos hr hn)
  have hdiv := div_le_div_of_nonneg_right hgamma (by positivity : 0 ≤ 12 * M ^ 2)
  calc
    separationBudgetConstant M r / (n : ℝ) ^ 2 =
        (((M ^ 2 - 1) / (4 * M ^ 2 + 1)) / ((r * n : ℕ) : ℝ) ^ 2) /
          (12 * M ^ 2) := by
      unfold separationBudgetConstant
      push_cast
      field_simp
    _ ≤ _ := hdiv

/-- The source's `ε = γ/(12M²)` and `κ = n³` satisfy the complete scalar
smallness condition eventually, while retaining the same exact M. -/
theorem eventually_separation_smallness {M : ℝ} {r : ℕ}
    (hM : 1 < M) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
      ((r * n : ℕ) : ℝ) *
          Real.exp (-(metricGamma M (r * n) / (12 * M ^ 2)) * (n : ℝ) ^ 3) ≤
        metricGamma M (r * n) / (12 * M ^ 2) := by
  let d := separationBudgetConstant M r
  have hd : 0 < d := separationBudgetConstant_pos hM hr
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 * Real.exp (-d * (n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 : ℕ) d hd).comp
        tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht.eventually_le_const (div_pos hd hrr)]
    with n hn hp
  refine ⟨hn, ?_⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hε : d / (n : ℝ) ^ 2 ≤ metricGamma M (r * n) / (12 * M ^ 2) :=
    separationBudget_lower hM hr (by omega)
  have hrate : d * (n : ℝ) ≤
      (metricGamma M (r * n) / (12 * M ^ 2)) * (n : ℝ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hε (by positivity : 0 ≤ (n : ℝ) ^ 3)
    have hcancel : (d / (n : ℝ) ^ 2) * (n : ℝ) ^ 3 = d * (n : ℝ) := by
      field_simp
    rwa [hcancel] at h
  calc
    ((r * n : ℕ) : ℝ) *
        Real.exp (-(metricGamma M (r * n) / (12 * M ^ 2)) * (n : ℝ) ^ 3) ≤
        ((r * n : ℕ) : ℝ) * Real.exp (-d * (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ d / (n : ℝ) ^ 2 := by
      apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) ^ 2)).mpr
      have hp' := mul_le_mul_of_nonneg_left hp hrr.le
      rw [mul_div_cancel₀ _ hrr.ne'] at hp'
      convert hp' using 1
      push_cast
      ring
    _ ≤ metricGamma M (r * n) / (12 * M ^ 2) := hε

end ProofProject
