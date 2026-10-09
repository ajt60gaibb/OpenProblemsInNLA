import ProofProject.ResolventAverage
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Normalized Gamma kernels for semigroup powers

The index `n` denotes Gamma shape `n + 1`. The rate is positive in all
integrability and mass statements, and the value on the nonpositive half-line
is zero. The shape-one kernel is the actual normalized resolvent kernel.
-/

noncomputable section

open MeasureTheory Set

namespace ProofProject

def gammaKernel (n : ℕ) (r u : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator
    (fun u => ((r ^ (n + 1) * Real.exp (-r * u) * u ^ n / (n.factorial : ℝ) : ℝ) : ℂ)) u

theorem gammaKernel_of_pos (n : ℕ) (r : ℝ) {u : ℝ} (hu : 0 < u) :
    gammaKernel n r u =
      ((r ^ (n + 1) * Real.exp (-r * u) * u ^ n / (n.factorial : ℝ) : ℝ) : ℂ) :=
  indicator_of_mem hu _

@[simp]
theorem gammaKernel_of_nonpos (n : ℕ) (r : ℝ) {u : ℝ} (hu : u ≤ 0) :
    gammaKernel n r u = 0 :=
  indicator_of_notMem (not_lt_of_ge hu) _

theorem gammaKernel_zero (r : ℝ) : gammaKernel 0 r = resolventKernel r := by
  funext u
  simp only [gammaKernel, resolventKernel, zero_add, pow_one, pow_zero,
    Nat.factorial_zero, Nat.cast_one, mul_one, div_one]

theorem norm_gammaKernel (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (u : ℝ) :
    ‖gammaKernel n r u‖ = (Ioi (0 : ℝ)).indicator
      (fun u => r ^ (n + 1) * Real.exp (-r * u) * u ^ n / (n.factorial : ℝ)) u := by
  by_cases hu : 0 < u
  · rw [gammaKernel_of_pos n r hu,
      indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu), Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · simp only [gammaKernel_of_nonpos n r (le_of_not_gt hu), norm_zero,
      indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu)]

theorem integral_gammaDensity (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ u : ℝ in Ioi 0,
      r ^ (n + 1) * Real.exp (-r * u) * u ^ n / (n.factorial : ℝ)) = 1 := by
  have hbase : (∫ u : ℝ in Ioi 0, u ^ n * Real.exp (-r * u)) =
      (1 / r) ^ (n + 1) * (n.factorial : ℝ) := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (show 0 < (n : ℝ) + 1 by positivity) hr
    rw [Real.Gamma_nat_eq_factorial, add_sub_cancel_right] at h
    simpa only [Real.rpow_natCast, neg_mul,
      ← Nat.cast_add_one] using h
  have heq : (fun u : ℝ =>
      r ^ (n + 1) * Real.exp (-r * u) * u ^ n / (n.factorial : ℝ)) =
      (fun u => (r ^ (n + 1) / (n.factorial : ℝ)) *
        (u ^ n * Real.exp (-r * u))) := by
    funext u
    ring
  rw [heq, integral_const_mul, hbase]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [div_pow, one_pow]
  field_simp [hr.ne']

theorem integral_gammaKernel (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ u : ℝ, gammaKernel n r u) = 1 := by
  unfold gammaKernel
  rw [integral_indicator measurableSet_Ioi, integral_complex_ofReal,
    integral_gammaDensity n hr]
  norm_num

theorem integral_norm_gammaKernel (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ u : ℝ, ‖gammaKernel n r u‖) = 1 := by
  simp_rw [norm_gammaKernel n hr.le]
  rw [integral_indicator measurableSet_Ioi, integral_gammaDensity n hr]

theorem gammaKernel_integrable (n : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (gammaKernel n r) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gammaKernel n hr]
  exact one_ne_zero

end ProofProject
