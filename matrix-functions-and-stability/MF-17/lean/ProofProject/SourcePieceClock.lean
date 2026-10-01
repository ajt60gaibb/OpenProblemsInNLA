import ProofProject.SourceSeparatorScale
import ProofProject.GrowthRate
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# A source-piece index controlled by the growth clock

The explicit ceiling places the first omitted scale beyond the observation
time. Its size is bounded by an absolute constant times the exact double
logarithm in the growth rate.
-/

noncomputable section

namespace ProofProject

def sourcePieceClockIndex (t : ℝ) : ℕ :=
  Nat.ceil (growthLog t / Real.log (4 / 3 : ℝ))

def sourcePieceClockConstant : ℝ := 1 + 1 / Real.log (4 / 3 : ℝ)

theorem sourcePieceClock_log_pos : 0 < Real.log (4 / 3 : ℝ) :=
  Real.log_pos (by norm_num)

theorem sourcePieceClockConstant_pos : 0 < sourcePieceClockConstant := by
  unfold sourcePieceClockConstant
  have h := sourcePieceClock_log_pos
  positivity

theorem sourcePieceClockIndex_ge_one {t : ℝ} (ht : 0 < t) :
    1 ≤ sourcePieceClockIndex t :=
  Nat.one_le_ceil_iff.mpr (div_pos (growthLog_pos ht.le) sourcePieceClock_log_pos)

theorem sourcePieceClockIndex_le {t : ℝ} (ht : 0 < t) :
    (sourcePieceClockIndex t : ℝ) ≤ sourcePieceClockConstant * growthLog t := by
  have harg : 0 ≤ growthLog t / Real.log (4 / 3 : ℝ) :=
    (div_pos (growthLog_pos ht.le) sourcePieceClock_log_pos).le
  calc
    _ ≤ growthLog t / Real.log (4 / 3 : ℝ) + 1 := (Nat.ceil_lt_add_one harg).le
    _ ≤ growthLog t / Real.log (4 / 3 : ℝ) + growthLog t :=
      add_le_add le_rfl (one_le_growthLog ht.le)
    _ = _ := by unfold sourcePieceClockConstant; ring

/-- The chosen index is already past `t + exp(exp 1)`, so no exact count of
the earlier piece scales is necessary. -/
theorem sourcePieceClockIndex_scale_lower {t : ℝ} (ht : 0 < t) :
    t + Real.exp (Real.exp 1) ≤ sourcePieceScale (sourcePieceClockIndex t) := by
  have hi : growthLog t / Real.log (4 / 3 : ℝ) ≤ (sourcePieceClockIndex t : ℝ) :=
    Nat.le_ceil _
  have hclock : growthLog t ≤ (sourcePieceClockIndex t : ℝ) * Real.log (4 / 3 : ℝ) :=
    (div_le_iff₀ sourcePieceClock_log_pos).mp hi
  have ht' := (growthLog_le_iff ht.le).mp hclock
  have hexp : Real.exp ((sourcePieceClockIndex t : ℝ) * Real.log (4 / 3 : ℝ)) =
      (4 / 3 : ℝ) ^ sourcePieceClockIndex t := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
  rw [hexp] at ht'
  have hL : 1 ≤ Real.log 16 := le_trans (by norm_num : (1 : ℝ) ≤ 2) two_le_log_sixteen
  calc
    _ ≤ Real.exp ((4 / 3 : ℝ) ^ sourcePieceClockIndex t) := ht'
    _ ≤ Real.exp (Real.log 16 * (4 / 3 : ℝ) ^ sourcePieceClockIndex t) := by
      apply Real.exp_le_exp.mpr
      exact le_mul_of_one_le_left (by positivity) hL
    _ = _ := (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 16) _).symm

theorem sourcePieceClockIndex_time_le_scale {t : ℝ} (ht : 0 < t) :
    t ≤ sourcePieceScale (sourcePieceClockIndex t) :=
  (le_add_of_nonneg_right (Real.exp_pos _).le).trans (sourcePieceClockIndex_scale_lower ht)

end ProofProject
