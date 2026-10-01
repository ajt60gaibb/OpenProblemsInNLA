import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The exact sector containing a disk about a positive real number

The disk `|q-w| ≤ ρ w`, with `w>0` and `0≤ρ<1`, lies in the right half-plane
and in the sector `sqrt(1-ρ²)|Im q| ≤ ρ Re q`. A completed-square identity
proves the sharp sector slope without a choice of complex argument.
-/

noncomputable section

namespace ProofProject

/-- The real-part estimate itself does not require sign assumptions on the
two real parameters. -/
theorem diskSector_re_lower {q : ℂ} {w ρ : ℝ}
    (hdisc : ‖q - (w : ℂ)‖ ≤ ρ * w) :
    (1 - ρ) * w ≤ q.re := by
  have hre := (abs_le.mp (Complex.abs_re_le_norm (q - (w : ℂ)))).1
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  linarith

/-- Exact squared sector bound from the disk inequality. -/
theorem diskSector_im_sq_le {q : ℂ} {w ρ : ℝ} (hw : 0 ≤ w)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hdisc : ‖q - (w : ℂ)‖ ≤ ρ * w) :
    (1 - ρ ^ 2) * q.im ^ 2 ≤ ρ ^ 2 * q.re ^ 2 := by
  have hd : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  have hn2 : (q.re - w) ^ 2 + q.im ^ 2 ≤ ρ ^ 2 * w ^ 2 := by
    have hsq := pow_le_pow_left₀ (norm_nonneg (q - (w : ℂ))) hdisc 2
    simpa only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
      mul_pow, ← sq] using hsq
  have hcomplete : ((1 - ρ ^ 2) * w - q.re) ^ 2 +
      ((1 - ρ ^ 2) * q.im ^ 2 - ρ ^ 2 * q.re ^ 2) =
      (1 - ρ ^ 2) * ((q.re - w) ^ 2 + q.im ^ 2 - ρ ^ 2 * w ^ 2) := by
    ring
  have hprod := mul_nonpos_of_nonneg_of_nonpos hd (sub_nonpos.mpr hn2)
  rw [← hcomplete] at hprod
  linarith [sq_nonneg ((1 - ρ ^ 2) * w - q.re)]

/-- The real-part lower bound, strict positivity, and sharp sector inequality
for a disk strictly contained in the right half-plane. -/
theorem diskSector_estimates {q : ℂ} {w ρ : ℝ} (hw : 0 < w)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hdisc : ‖q - (w : ℂ)‖ ≤ ρ * w) :
    (1 - ρ) * w ≤ q.re ∧ 0 < q.re ∧
      Real.sqrt (1 - ρ ^ 2) * |q.im| ≤ ρ * q.re := by
  have hre := diskSector_re_lower hdisc
  have hre0 : 0 < q.re := (mul_pos (sub_pos.mpr hρ1) hw).trans_le hre
  refine ⟨hre, hre0, ?_⟩
  have hd : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    (mul_nonneg hρ0 hre0.le)).mp
  simpa only [mul_pow, Real.sq_sqrt hd, sq_abs] using
    diskSector_im_sq_le hw.le hρ0 hρ1.le hdisc

/-- The exact source parameter turns the square-root sector coefficient into
`1/K`, so the slope is `K * sqrt(1-K⁻²)`. -/
theorem diskSector_growthParameter {q : ℂ} {w K : ℝ} (hK : 1 < K)
    (hw : 0 < w)
    (hdisc : ‖q - (w : ℂ)‖ ≤ Real.sqrt (1 - K⁻¹ ^ 2) * w) :
    (1 - Real.sqrt (1 - K⁻¹ ^ 2)) * w ≤ q.re ∧ 0 < q.re ∧
      |q.im| ≤ K * Real.sqrt (1 - K⁻¹ ^ 2) * q.re := by
  have hK0 : 0 < K := lt_trans zero_lt_one hK
  have hi0 : 0 < K⁻¹ := inv_pos.mpr hK0
  have hi1 : K⁻¹ < 1 := (inv_lt_one₀ hK0).mpr hK
  have hd : 0 ≤ 1 - K⁻¹ ^ 2 := by nlinarith
  have hρ0 := Real.sqrt_nonneg (1 - K⁻¹ ^ 2)
  have hρ2 := Real.sq_sqrt hd
  have hρ1 : Real.sqrt (1 - K⁻¹ ^ 2) < 1 := by nlinarith [sq_pos_of_pos hi0]
  obtain ⟨hre, hre0, him⟩ := diskSector_estimates hw hρ0 hρ1 hdisc
  refine ⟨hre, hre0, ?_⟩
  have hsqrt : Real.sqrt (1 - Real.sqrt (1 - K⁻¹ ^ 2) ^ 2) = K⁻¹ := by
    rw [hρ2, show 1 - (1 - K⁻¹ ^ 2) = K⁻¹ ^ 2 by ring, Real.sqrt_sq hi0.le]
  rw [hsqrt] at him
  calc
    |q.im| = K * (K⁻¹ * |q.im|) := by
      rw [← mul_assoc, mul_inv_cancel₀ hK0.ne', one_mul]
    _ ≤ K * (Real.sqrt (1 - K⁻¹ ^ 2) * q.re) :=
      mul_le_mul_of_nonneg_left him hK0.le
    _ = _ := by ring

end ProofProject
