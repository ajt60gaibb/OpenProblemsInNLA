import ProofProject.SourcePieceScale
import ProofProject.FiniteGeometricError
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite tails of the source damping factors

Once the source scale reaches the time parameter, subsequent damping factors
are bounded by a geometric sequence whose finite sum is at most one.
-/

noncomputable section

namespace ProofProject

open Finset

/-- The doubling estimate implies this weaker, convenient linear growth bound. -/
theorem sourcePieceScale_linear_growth (k j : ℕ) :
    ((j : ℝ) + 1) * sourcePieceScale k ≤ sourcePieceScale (k + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hdouble := sourcePieceScale_double_le (k + j)
      have hmono := sourcePieceScale_monotone (Nat.le_add_right k j)
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show k + (j + 1) = (k + j) + 1 by omega]
      linarith

/-- A pointwise geometric majorant starting at any scale above the time. -/
theorem sourcePiece_damping_le_geometric (k j : ℕ) {t : ℝ}
    (ht : 0 < t) (htk : t ≤ sourcePieceScale k) :
    Real.exp (-sourcePieceScale (k + j) / t) ≤ (1 / 2 : ℝ) ^ (j + 1) := by
  have hratio : (j : ℝ) + 1 ≤ sourcePieceScale (k + j) / t := by
    apply (le_div_iff₀ ht).mpr
    exact (mul_le_mul_of_nonneg_left htk (by positivity)).trans
      (sourcePieceScale_linear_growth k j)
  have hbase : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) htwo
  calc
    _ ≤ Real.exp (-((j : ℝ) + 1)) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg hratio
    _ = Real.exp (-1) ^ (j + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ ≤ (1 / 2 : ℝ) ^ (j + 1) :=
      pow_le_pow_left₀ (Real.exp_pos _).le hbase _

/-- The geometric majorant has total mass at most one, for every finite length. -/
theorem sum_sourcePiece_damping_shift_le_one (k m : ℕ) {t : ℝ}
    (ht : 0 < t) (htk : t ≤ sourcePieceScale k) :
    (∑ j ∈ range m, Real.exp (-sourcePieceScale (k + j) / t)) ≤ 1 := by
  have hsum : (∑ j ∈ range m, (1 / 2 : ℝ) ^ j) ≤ 1 / (1 - (1 / 2 : ℝ)) := by
    simpa only [id_eq] using sum_geometric_injOn_le (range m) id
      Function.injective_id.injOn (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
  calc
    _ ≤ ∑ j ∈ range m, (1 / 2 : ℝ) ^ (j + 1) :=
      sum_le_sum (fun j _ => sourcePiece_damping_le_geometric k j ht htk)
    _ = (1 / 2 : ℝ) * ∑ j ∈ range m, (1 / 2 : ℝ) ^ j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      rw [pow_succ, mul_comm]
    _ ≤ (1 / 2 : ℝ) * (1 / (1 - (1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 1 := by norm_num

/-- Every finite damping tail beyond a scale above the time has mass at most one.
No ordering assumption on the two endpoints is needed. -/
theorem sum_sourcePiece_damping_Ico_le_one (k m : ℕ) {t : ℝ}
    (ht : 0 < t) (htk : t ≤ sourcePieceScale k) :
    (∑ q ∈ Ico k m, Real.exp (-sourcePieceScale q / t)) ≤ 1 := by
  rw [sum_Ico_eq_sum_range]
  exact sum_sourcePiece_damping_shift_le_one k (m - k) ht htk

end ProofProject
