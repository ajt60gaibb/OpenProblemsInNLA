import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# A quantitative cosine margin

Jordan's sine inequality and monotonicity on the first quadrant turn a positive
angular decrement `E` into a linear lower bound for the cosine deficit. The
statements are independent of any particular analytic phase construction.
-/

namespace ProofProject

/-- The linear cosine-margin prefactor is strictly positive inside the first
quadrant. -/
theorem cosine_margin_coefficient_pos {β : ℝ} (hβ0 : 0 < β) (hβπ : β < Real.pi / 2) :
    0 < (4 / Real.pi) * Real.cos β * Real.sin (β / 2) := by
  have hcos : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβπ⟩
  have hsin : 0 < Real.sin (β / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact mul_pos (mul_pos (div_pos (by norm_num) Real.pi_pos) hcos) hsin

/-- A phase decrement in `[0,β]` gives the source's explicit linear cosine
margin, with coefficient `(4/π) cos β sin(β/2)`. -/
theorem cosine_margin_lower {β E : ℝ} (hβ0 : 0 < β) (hβπ : β < Real.pi / 2)
    (hE0 : 0 ≤ E) (hEβ : E ≤ β) :
    (4 / Real.pi) * Real.cos β * Real.sin (β / 2) * E ≤
      2 * Real.cos β * (Real.cos (β - E) - Real.cos β) := by
  have hcos : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβπ⟩
  have hsin : 0 < Real.sin (β / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsmall : E / Real.pi ≤ Real.sin (E / 2) := by
    convert Real.mul_le_sin (by linarith : 0 ≤ E / 2)
      (by linarith : E / 2 ≤ Real.pi / 2) using 1
    ring
  have hsmall_nonneg : 0 ≤ Real.sin (E / 2) :=
    (div_nonneg hE0 Real.pi_pos.le).trans hsmall
  have hlarge : Real.sin (β / 2) ≤ Real.sin (β - E / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith) (by linarith)
  have hproduct := mul_le_mul hsmall hlarge hsin.le hsmall_nonneg
  have hidentity : Real.cos (β - E) - Real.cos β =
      2 * Real.sin (E / 2) * Real.sin (β - E / 2) := by
    rw [Real.cos_sub_cos,
      show (β - E + β) / 2 = β - E / 2 by ring,
      show (β - E - β) / 2 = -(E / 2) by ring, Real.sin_neg]
    ring
  calc
    _ = (4 * Real.cos β) * ((E / Real.pi) * Real.sin (β / 2)) := by ring
    _ ≤ (4 * Real.cos β) * (Real.sin (E / 2) * Real.sin (β - E / 2)) :=
      mul_le_mul_of_nonneg_left hproduct (by positivity)
    _ = _ := by rw [hidentity]; ring

/-- Every positive decrement in the allowed range gives a strictly positive
phase margin. -/
theorem cosine_margin_pos {β E : ℝ} (hβ0 : 0 < β) (hβπ : β < Real.pi / 2)
    (hE0 : 0 < E) (hEβ : E ≤ β) :
    0 < 2 * Real.cos β * (Real.cos (β - E) - Real.cos β) :=
  (mul_pos (cosine_margin_coefficient_pos hβ0 hβπ) hE0).trans_le
    (cosine_margin_lower hβ0 hβπ hE0.le hEβ)

end ProofProject
