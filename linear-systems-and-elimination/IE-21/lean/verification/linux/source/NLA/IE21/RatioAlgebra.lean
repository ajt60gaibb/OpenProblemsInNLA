import NLA.IE21.FiniteTrimming
import Mathlib.Tactic

/-! Exact denominator control for the IE-21 ratio statistic.
Original analytic argument: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology. -/
set_option autoImplicit false
noncomputable section
namespace NLA.IE21

lemma ratio_stability (u v h e t : ℝ) (hh : 0 ≤ h ∧ h ≤ 1)
    (hu : |u - h| ≤ e) (hv : |v - 1| ≤ t) (ht : t < 1) :
    0 < v ∧ |u / v - h| ≤ (e + t) / (1 - t) := by
  have he : 0 ≤ e := (abs_nonneg _).trans hu
  have ht0 : 0 ≤ t := (abs_nonneg _).trans hv
  have hden : 1 - t ≤ v := by have hv' := (abs_le.mp hv).1; linarith
  have hdenpos : 0 < 1 - t := by linarith
  have hvpos : 0 < v := hdenpos.trans_le hden
  refine ⟨hvpos, ?_⟩
  have hprod : |h * (1 - v)| ≤ t := by
    rw [abs_mul, abs_of_nonneg hh.1, abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left hv hh.1).trans
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) ht0])
  have hnum : |u - h * v| ≤ e + t := by
    have heq : u - h * v = (u - h) + h * (1 - v) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add hu hprod)
  have heq : u / v - h = (u - h * v) / v := by field_simp
  rw [heq, abs_div, abs_of_pos hvpos]
  exact (div_le_div_of_nonneg_right hnum hvpos.le).trans
    (div_le_div_of_nonneg_left (by positivity) hdenpos hden)

lemma deletionRatio_eq_normalized {m n : ℕ} (θ : ℝ) (A : Mat m n)
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    deletionRatio θ A = normalizedDeletion θ A / normalizedOperator A := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold deletionRatio normalizedDeletion normalizedOperator
  rw [mul_div_mul_left _ _ (div_ne_zero hnR hmR)]

end NLA.IE21
