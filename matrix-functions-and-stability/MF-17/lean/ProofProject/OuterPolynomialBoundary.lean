import ProofProject.GrowthRate
import ProofProject.PolynomialRadialMaximum

/-!
# The finite scalar boundary estimate from an interior estimate

The radius `1-1/(n+1)` treats `n=1` and larger dimensions uniformly. It gives
the absolute constant `16*exp(2)` while preserving the exact growth exponent.
The analytic interior estimate is an explicit premise of this final step.
-/

noncomputable section

namespace ProofProject

/-- The source interior estimate implies the polynomial boundary estimate
at every point of the unit circle, with one absolute constant. -/
theorem outerPolynomial_unitCircle_bound (p : Polynomial ℂ) {K : ℝ} (hK : 1 < K)
    {n : ℕ} (hn : 1 ≤ n) (hdeg : p.natDegree ≤ n - 1) {W : ℝ} (hW : 0 ≤ W)
    (hinside : ∀ z : ℂ, ‖z‖ < 1 →
      ‖p.eval z‖ ^ 2 ≤ 4 * K ^ 2 * ((1 + ‖z‖) / (1 - ‖z‖)) ^ growthExponent K * W)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖p.eval z‖ ^ 2 ≤ (16 * Real.exp 2) * K ^ 2 * (n : ℝ) ^ growthExponent K * W := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  let r : ℝ := 1 - 1 / ((n : ℝ) + 1)
  have hr0 : 0 < r := by
    dsimp only [r]
    exact sub_pos.mpr ((div_lt_one hnpos).mpr (by linarith))
  have hr1 : r < 1 := by
    dsimp only [r]
    exact sub_lt_self _ (one_div_pos.mpr hnpos)
  have hratio : (1 + r) / (1 - r) = 2 * (n : ℝ) + 1 := by
    have hden : 1 - r = 1 / ((n : ℝ) + 1) := by dsimp only [r]; ring
    rw [hden]
    dsimp only [r]
    field_simp [hnpos.ne']
    ring
  have hratio0 : 0 ≤ (1 + r) / (1 - r) := by rw [hratio]; positivity
  have hratio4 : (1 + r) / (1 - r) ≤ 4 * (n : ℝ) := by rw [hratio]; linarith
  have hα0 : 0 ≤ growthExponent K := growthExponent_nonneg K
  have hα1 : growthExponent K ≤ 1 := (growthExponent_lt_one (zero_lt_one.trans hK)).le
  have hfour : (4 : ℝ) ^ growthExponent K ≤ 4 := by
    calc
      _ ≤ (4 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
      _ = 4 := Real.rpow_one _
  have hpower : ((1 + r) / (1 - r)) ^ growthExponent K ≤
      4 * (n : ℝ) ^ growthExponent K := by
    calc
      _ ≤ (4 * (n : ℝ)) ^ growthExponent K := Real.rpow_le_rpow hratio0 hratio4 hα0
      _ = (4 : ℝ) ^ growthExponent K * (n : ℝ) ^ growthExponent K :=
        Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  let A : ℝ := 4 * K ^ 2 * ((1 + r) / (1 - r)) ^ growthExponent K * W
  have hA0 : 0 ≤ A := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (Real.rpow_nonneg hratio0 _)) hW
  have hcircle : ∀ w : ℂ, ‖w‖ = r → ‖p.eval w‖ ^ 2 ≤ A := by
    intro w hw
    have hb := hinside w (hw.trans_lt hr1)
    simpa only [hw, A] using hb
  have hinv : r⁻¹ ^ (2 * (n - 1)) ≤ Real.exp 2 := by
    simpa only [r, Nat.cast_add, Nat.cast_one] using
      source_radius_inverse_pow_le_exp_two (n := n + 1) (d := n - 1) (by omega) (by omega)
  calc
    _ ≤ r⁻¹ ^ (2 * (n - 1)) * A :=
      polynomial_radial_maximum_sq_inv p hdeg hr0 hr1.le hcircle hz
    _ ≤ Real.exp 2 * A := mul_le_mul_of_nonneg_right hinv hA0
    _ ≤ Real.exp 2 * (4 * K ^ 2 * (4 * (n : ℝ) ^ growthExponent K) * W) := by
      apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower (by positivity)) hW
    _ = _ := by ring

theorem outerPolynomial_boundary_bound (p : Polynomial ℂ) {K : ℝ} (hK : 1 < K)
    {n : ℕ} (hn : 1 ≤ n) (hdeg : p.natDegree ≤ n - 1) {W : ℝ} (hW : 0 ≤ W)
    (hinside : ∀ z : ℂ, ‖z‖ < 1 →
      ‖p.eval z‖ ^ 2 ≤ 4 * K ^ 2 * ((1 + ‖z‖) / (1 - ‖z‖)) ^ growthExponent K * W) :
    ‖p.eval 1‖ ^ 2 ≤ (16 * Real.exp 2) * K ^ 2 * (n : ℝ) ^ growthExponent K * W :=
  outerPolynomial_unitCircle_bound p hK hn hdeg hW hinside (by simp)

end ProofProject
