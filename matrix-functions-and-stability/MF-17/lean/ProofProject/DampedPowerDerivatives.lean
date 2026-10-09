import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Derivatives of the power times exponential amplitude

All estimates are on the positive half-line. A cutoff supported away from zero
will supply global smoothness of the source pieces. The derivative constants
are independent of the damping time and the lower support scale.
-/

noncomputable section

open Set Filter Finset
open scoped Topology ContDiff

namespace ProofProject

def rpowDerivativeCoefficient (β : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ range n, (β - j)

theorem iteratedDeriv_rpow_pos (β : ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv n (fun v : ℝ => v ^ β) u =
      rpowDerivativeCoefficient β n * u ^ (β - n) := by
  induction n generalizing u with
  | zero => simp [rpowDerivativeCoefficient]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun v : ℝ => v ^ β) =ᶠ[𝓝 u]
        fun v => rpowDerivativeCoefficient β n * v ^ (β - n) := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact ih hv
    rw [heq.deriv_eq]
    rw [((Real.hasDerivAt_rpow_const (p := β - n) (Or.inl hu.ne')).const_mul
      (rpowDerivativeCoefficient β n)).deriv]
    simp only [rpowDerivativeCoefficient, prod_range_succ, Nat.cast_add, Nat.cast_one]
    rw [show β - (n : ℝ) - 1 = β - ((n : ℝ) + 1) by ring]
    ring

/-- Half of the exponential absorbs any fixed power, with an explicit constant. -/
theorem pow_mul_exp_neg_le_half (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    z ^ n * Real.exp (-z) ≤
      (2 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (-z / 2) := by
  have ht := Real.pow_div_factorial_le_exp (z / 2) (div_nonneg hz (by norm_num : (0 : ℝ) ≤ 2)) n
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have hp : z ^ n ≤ (2 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (z / 2) := by
    rw [div_le_iff₀ hfac] at ht
    have hh := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 2 ^ n)
    rw [div_pow] at hh
    field_simp at hh
    nlinarith
  calc
    _ ≤ ((2 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (z / 2)) * Real.exp (-z) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem pow_mul_exp_neg_le_damping (n : ℕ) {t N u : ℝ}
    (ht : 0 < t) (hu : 0 ≤ u) (hNu : 2 * N ≤ u) :
    (u / t) ^ n * Real.exp (-u / t) ≤
      (2 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (-N / t) := by
  have h := pow_mul_exp_neg_le_half n (div_nonneg hu ht.le)
  have hz : -(u / t) / 2 ≤ -N / t := by
    have hh := (div_le_div_iff_of_pos_right ht).mpr hNu
    rw [mul_div_assoc] at hh
    simp only [neg_div]
    linarith
  simpa only [neg_div] using h.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz) (by positivity))

def dampedPower (β t u : ℝ) : ℝ := u ^ β * Real.exp (-u / t)

theorem dampedPower_contDiffAt (β t : ℝ) {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ ∞ (dampedPower β t) u := by
  apply ContDiffAt.mul
  · exact Real.contDiffAt_rpow_const_of_ne hu.ne'
  · fun_prop

theorem iteratedDeriv_dampedPower (β t : ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv n (dampedPower β t) u =
      ∑ i ∈ range (n + 1), (n.choose i : ℝ) *
        (rpowDerivativeCoefficient β i * u ^ (β - i)) *
        ((-1 / t) ^ (n - i) * Real.exp (-u / t)) := by
  have hpow : ContDiffAt ℝ n (fun v : ℝ => v ^ β) u :=
    Real.contDiffAt_rpow_const_of_ne hu.ne'
  have hexp : ContDiffAt ℝ n (fun v : ℝ => Real.exp ((-1 / t) * v)) u := by fun_prop
  have heq : dampedPower β t =
      (fun v : ℝ => v ^ β) * (fun v => Real.exp ((-1 / t) * v)) := by
    funext v
    simp only [dampedPower, Pi.mul_apply]
    congr 2
    ring
  rw [heq, iteratedDeriv_mul hpow hexp]
  apply sum_congr rfl
  intro i hi
  rw [iteratedDeriv_rpow_pos β i hu, iteratedDeriv_exp_const_mul]
  simp only [show (-1 / t) * u = -u / t by ring]

def dampedPowerDerivativeBound (β : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (n + 1), (n.choose i : ℝ) * |rpowDerivativeCoefficient β i| *
    (2 : ℝ) ^ (n - i) * ((n - i).factorial : ℝ)

theorem dampedPowerDerivativeBound_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ dampedPowerDerivativeBound β n := by
  apply sum_nonneg
  intro i hi
  positivity

private theorem rpow_shift_nat {u β : ℝ} (hu : 0 < u) {i n : ℕ} (hi : i ≤ n) :
    u ^ (β - i) = u ^ (β - n) * u ^ (n - i) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hu]
  congr 1
  rw [Nat.cast_sub hi]
  ring

/-- Uniform weighted estimates for every derivative order. The factor
`exp (-N/t)` is retained, since the orbit piece begins at `u ≥ 2N`. -/
theorem norm_iteratedDeriv_dampedPower_le (β : ℝ) (n : ℕ) {t N u : ℝ}
    (ht : 0 < t) (hu : 0 < u) (hNu : 2 * N ≤ u) :
    ‖iteratedDeriv n (dampedPower β t) u‖ ≤
      dampedPowerDerivativeBound β n * Real.exp (-N / t) * u ^ (β - n) := by
  rw [iteratedDeriv_dampedPower β t n hu]
  calc
    _ ≤ ∑ i ∈ range (n + 1), ‖(n.choose i : ℝ) *
        (rpowDerivativeCoefficient β i * u ^ (β - i)) *
        ((-1 / t) ^ (n - i) * Real.exp (-u / t))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range (n + 1),
        ((n.choose i : ℝ) * |rpowDerivativeCoefficient β i| *
          (2 : ℝ) ^ (n - i) * ((n - i).factorial : ℝ)) *
          Real.exp (-N / t) * u ^ (β - n) := by
      apply sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
      have hnorm : ‖(n.choose i : ℝ) *
          (rpowDerivativeCoefficient β i * u ^ (β - i)) *
          ((-1 / t) ^ (n - i) * Real.exp (-u / t))‖ =
          ((n.choose i : ℝ) * |rpowDerivativeCoefficient β i| * u ^ (β - n)) *
            ((u / t) ^ (n - i) * Real.exp (-u / t)) := by
        simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_div, abs_one,
          abs_of_pos ht, abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (Real.rpow_nonneg hu.le _), abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n.choose i))]
        rw [rpow_shift_nat hu hin]
        simp only [div_pow, one_pow]
        ring
      rw [hnorm]
      have h := mul_le_mul_of_nonneg_left
        (pow_mul_exp_neg_le_damping (n - i) ht hu.le hNu)
        (by positivity : 0 ≤ (n.choose i : ℝ) * |rpowDerivativeCoefficient β i| *
          u ^ (β - n))
      convert h using 1; ring
    _ = _ := by
      simp only [dampedPowerDerivativeBound, sum_mul]

end ProofProject
