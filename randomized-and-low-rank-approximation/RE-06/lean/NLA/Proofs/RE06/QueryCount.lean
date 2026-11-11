import NLA.Computation.NonadaptiveMatrixQuery
import LeanCert.Tactic.Verification

/-! Worst-case query count for the unchanged precommitted RE-06 query list.
The estimates are deliberately uniform in every Gaussian stream. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 2000

namespace NLA.Proofs.RE06
open NLA.Computation.NonadaptiveMatrixQuery

namespace Counts

theorem queryList_length {n : ℕ} (P : Plan n) :
    (queryList P).length = if P.full then n else P.s + P.k + P.ell := by
  unfold queryList
  split <;> simp_all [Nat.add_assoc]

theorem makePlan_query_count (n m : ℕ) (ε : ℝ) (ω : ℕ → ℝ) :
    (queryList (makePlan n m ε ω)).length =
      min n (firstWidth m ε + secondWidth m ε + thirdWidth m ε) := by
  rw [queryList_length]
  by_cases h : n ≤ firstWidth m ε + secondWidth m ε + thirdWidth m ε
  · simp [makePlan, h]
  · simp [makePlan, h, Nat.min_eq_right (Nat.le_of_not_ge h)]

theorem logWidth_pos (m : ℕ) : 0 < logWidth m := by
  exact Nat.clog_pos (by norm_num) (by omega)

theorem rootWidth_pos (m : ℕ) : 0 < rootWidth m := by
  have h := Nat.sqrt_pos.mpr (logWidth_pos m)
  dsimp only [rootWidth]
  split <;> omega

theorem logWidth_le_root_sq (m : ℕ) : logWidth m ≤ rootWidth m ^ 2 := by
  dsimp only [rootWidth]
  split
  · exact (Nat.lt_succ_sqrt' _).le
  · omega

theorem rootWidth_le_sqrt_add_one (m : ℕ) :
    rootWidth m ≤ Nat.sqrt (logWidth m) + 1 := by
  dsimp only [rootWidth]
  split <;> omega

theorem log_size_ge_one (m : ℕ) : 1 ≤ Real.log (2 * (m + 2 : ℕ)) := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  have h4 : (4 : ℝ) ≤ (2 * (m + 2 : ℕ) : ℕ) := by exact_mod_cast (show 4 ≤ 2 * (m + 2) by omega)
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4
  have heq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := Real.log_pow _ _
  push_cast at hmono ⊢
  linarith

theorem logWidth_le_two_log_add_one (m : ℕ) :
    (logWidth m : ℝ) ≤ 2 * Real.log (2 * (m + 2 : ℕ)) + 1 := by
  have hx : (0 : ℝ) ≤ Real.log (2 * (m + 2 : ℕ)) := by
    linarith [log_size_ge_one m]
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  have h2p : 0 < Real.log 2 := by linarith
  have hb : (0 : ℝ) ≤ Real.logb 2 (2 * (m + 2 : ℕ)) := by
    unfold Real.logb
    exact div_nonneg hx h2p.le
  have heq : Nat.ceil (Real.logb 2 (2 * (m + 2 : ℕ))) = logWidth m := by
    simpa [logWidth] using Real.natCeil_logb_natCast 2 (2 * (m + 2))
  have hc := (Nat.ceil_lt_add_one hb).le
  rw [heq] at hc
  have hdiv : Real.logb 2 (2 * (m + 2 : ℕ)) ≤
      2 * Real.log (2 * (m + 2 : ℕ)) := by
    unfold Real.logb
    apply (div_le_iff₀ h2p).mpr
    nlinarith
  linarith

theorem rootWidth_le_three_sqrt_log (m : ℕ) :
    (rootWidth m : ℝ) ≤ 3 * Real.sqrt (Real.log (2 * (m + 2 : ℕ))) := by
  let t := Real.log (2 * (m + 2 : ℕ))
  have ht : 1 ≤ t := log_size_ge_one m
  have hsq := Real.sq_sqrt (show 0 ≤ t by linarith)
  have hnon := Real.sqrt_nonneg t
  have hone : 1 ≤ Real.sqrt t := by nlinarith
  have hL := logWidth_le_two_log_add_one m
  have hq : (Nat.sqrt (logWidth m) : ℝ) ^ 2 ≤ logWidth m := by
    exact_mod_cast Nat.sqrt_le' (logWidth m)
  have hqn : (0 : ℝ) ≤ Nat.sqrt (logWidth m) := Nat.cast_nonneg _
  have hqbound : (Nat.sqrt (logWidth m) : ℝ) ≤ 2 * Real.sqrt t := by
    change (logWidth m : ℝ) ≤ 2 * t + 1 at hL
    nlinarith
  have hr : (rootWidth m : ℝ) ≤ (Nat.sqrt (logWidth m) : ℝ) + 1 := by
    exact_mod_cast rootWidth_le_sqrt_add_one m
  change (rootWidth m : ℝ) ≤ 3 * Real.sqrt t
  linarith

#assert_trust kernel makePlan_query_count
#assert_trust kernel rootWidth_le_three_sqrt_log
#print axioms rootWidth_le_three_sqrt_log
end Counts
end NLA.Proofs.RE06
