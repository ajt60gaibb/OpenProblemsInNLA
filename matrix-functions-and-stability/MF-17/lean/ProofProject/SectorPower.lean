import ProofProject.GrowthRate
import ProofProject.HalfPlaneRadial
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The exact growth exponent from an analytic sector

The sector with slope `K * sqrt(1-K⁻²)` has half-angle `arccos(K⁻¹)`.
Raising a function in that sector to the principal power `1/growthExponent K`
maps it to the closed right half-plane. The half-plane radial estimate then
returns the source radial estimate with exactly `growthExponent K`.
-/

noncomputable section

open Metric Set

namespace ProofProject

/-- The source sector has the precise half-angle defining the target exponent. -/
theorem sector_arg_le {K : ℝ} {q : ℂ} (hK : 1 < K) (hre : 0 < q.re)
    (hsector : |q.im| ≤ K * Real.sqrt (1 - K⁻¹ ^ 2) * q.re) :
    |q.arg| ≤ Real.arccos K⁻¹ := by
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hb0 : 0 ≤ Real.arccos K⁻¹ := Real.arccos_nonneg _
  have hb1 : Real.arccos K⁻¹ < Real.pi / 2 :=
    Real.arccos_lt_pi_div_two.mpr (inv_pos.mpr hK0)
  have hb : Real.arccos K⁻¹ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], hb1⟩
  have ha := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hai : q.arg ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := abs_lt.mp ha
  have hani : -q.arg ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hai.1, hai.2]
  have htan : Real.tan (Real.arccos K⁻¹) = K * Real.sqrt (1 - K⁻¹ ^ 2) := by
    rw [Real.tan_arccos, div_eq_mul_inv, inv_inv, mul_comm]
  have ht : Real.tan q.arg ≤ Real.tan (Real.arccos K⁻¹) := by
    rw [Complex.tan_arg, htan]
    apply (div_le_iff₀ hre).mpr
    exact (le_abs_self q.im).trans hsector
  have hnt : Real.tan (-q.arg) ≤ Real.tan (Real.arccos K⁻¹) := by
    rw [Real.tan_neg, Complex.tan_arg, htan, ← neg_div]
    apply (div_le_iff₀ hre).mpr
    exact (neg_le_abs q.im).trans hsector
  have hupper := (Real.strictMonoOn_tan.le_iff_le hai hb).mp ht
  have hlower := (Real.strictMonoOn_tan.le_iff_le hani hb).mp hnt
  exact abs_le.mpr ⟨by linarith, hupper⟩

/-- Scaling the exact sector angle by the reciprocal exponent gives π/2. -/
lemma sector_angle_mul_growthExponent_inv {K : ℝ} (hK : 1 < K) :
    Real.arccos K⁻¹ * (growthExponent K)⁻¹ = Real.pi / 2 := by
  have ha : growthExponent K ≠ 0 := (growthExponent_pos hK).ne'
  have hid : Real.arccos K⁻¹ = growthExponent K * (Real.pi / 2) := by
    unfold growthExponent
    rw [one_div]
    field_simp
  rw [hid]
  calc
    _ = (growthExponent K * (growthExponent K)⁻¹) * (Real.pi / 2) := by ring
    _ = _ := by rw [mul_inv_cancel₀ ha, one_mul]

/-- The principal sector power has nonnegative real part, including points on
the boundary rays of the sector. -/
theorem sectorPower_re_nonneg {K : ℝ} {q : ℂ} (hK : 1 < K) (hre : 0 < q.re)
    (hsector : |q.im| ≤ K * Real.sqrt (1 - K⁻¹ ^ 2) * q.re) :
    0 ≤ (q ^ (((growthExponent K)⁻¹ : ℝ) : ℂ)).re := by
  have ha : 0 < growthExponent K := growthExponent_pos hK
  have harg := sector_arg_le hK hre hsector
  have hscaled := mul_le_mul_of_nonneg_right harg (inv_nonneg.mpr ha.le)
  rw [sector_angle_mul_growthExponent_inv hK] at hscaled
  have hangle : |q.arg * (growthExponent K)⁻¹| ≤ Real.pi / 2 := by
    simpa only [abs_mul, abs_of_pos (inv_pos.mpr ha)] using hscaled
  rw [Complex.cpow_ofReal_re]
  exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.cos_nonneg_of_mem_Icc (abs_le.mp hangle))

/-- The exact radial estimate supplied by the source sector. Neither the
projection constant nor the target exponent is enlarged. -/
theorem sector_growth_norm_le {K : ℝ} {q : ℂ → ℂ} (hK : 1 < K)
    (hq : DifferentiableOn ℂ q (ball 0 1))
    (hRe : ∀ w : ℂ, ‖w‖ < 1 → 0 < (q w).re)
    (hSector : ∀ w : ℂ, ‖w‖ < 1 →
      |(q w).im| ≤ K * Real.sqrt (1 - K⁻¹ ^ 2) * (q w).re)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖q z‖ ≤ ‖q 0‖ * ((1 + ‖z‖) / (1 - ‖z‖)) ^ growthExponent K := by
  let F : ℂ → ℂ := fun w => q w ^ (((growthExponent K)⁻¹ : ℝ) : ℂ)
  have hF : DifferentiableOn ℂ F (ball 0 1) :=
    hq.cpow_const (fun w hw => Complex.mem_slitPlane_iff.mpr
      (Or.inl (hRe w (mem_ball_zero_iff.mp hw))))
  have hFre : ∀ w : ℂ, ‖w‖ < 1 → 0 ≤ (F w).re :=
    fun w hw => sectorPower_re_nonneg hK (hRe w hw) (hSector w hw)
  have hb := halfPlane_norm_le hF hFre hz
  simp only [F, Complex.norm_cpow_real] at hb
  have hratio : 0 ≤ (1 + ‖z‖) / (1 - ‖z‖) :=
    div_nonneg (by positivity) (sub_pos.mpr hz).le
  have hmul : ‖q z‖ ^ (growthExponent K)⁻¹ ≤
      ‖q 0‖ ^ (growthExponent K)⁻¹ * ((1 + ‖z‖) / (1 - ‖z‖)) := by
    simpa only [mul_div_assoc] using hb
  have hraised := Real.rpow_le_rpow
    (Real.rpow_nonneg (norm_nonneg (q z)) _) hmul (growthExponent_nonneg K)
  rw [Real.rpow_inv_rpow (norm_nonneg (q z)) (growthExponent_pos hK).ne',
    Real.mul_rpow (Real.rpow_nonneg (norm_nonneg (q 0)) _) hratio,
    Real.rpow_inv_rpow (norm_nonneg (q 0)) (growthExponent_pos hK).ne'] at hraised
  exact hraised

end ProofProject
