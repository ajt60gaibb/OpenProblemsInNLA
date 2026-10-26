import NLA.Proofs.RE06.GaussianWarmStartResidual
import NLA.Proofs.RE06.QueryCount

/-! The source's explicit warm-start failure budget for the frozen widths. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Matrix
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

theorem gaussian_logWidth_ge_two (m : ℕ) : 2 ≤ logWidth m := by
  by_contra h
  have hL : logWidth m ≤ 1 := by omega
  have hM : 2 * (m + 2) ≤ 2 ^ 1 :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp hL
  norm_num at hM
  omega

theorem gaussian_size_exp_bound (m : ℕ) :
    (m + 2 : ℝ) * Real.exp (-8 * (logWidth m : ℝ)) ≤ 2 * Real.exp (-16) := by
  have hL : (2 : ℝ) ≤ logWidth m := by exact_mod_cast gaussian_logWidth_ge_two m
  have hMp : (0 : ℝ) < (m + 2 : ℝ) := by positivity
  have hpow : 2 * (m + 2 : ℝ) ≤ (2 : ℝ) ^ logWidth m := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (2 * (m + 2))
  have hlog := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 2) hMp) hpow
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hMp.ne', Real.log_pow] at hlog
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hprod := mul_le_mul_of_nonneg_left htwo (show 0 ≤ (logWidth m : ℝ) - 2 by linarith)
  calc
    _ = Real.exp (Real.log (m + 2 : ℝ) - 8 * (logWidth m : ℝ)) := by
      rw [Real.exp_sub, Real.exp_log hMp, Real.exp_neg]
      ring
    _ ≤ Real.exp (Real.log 2 - 16) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_neg]; ring

theorem gaussian_firstWidth_lower (m : ℕ) (ε : ℝ) :
    32 * (logWidth m : ℝ) / ((rootWidth m : ℝ) * (ε / 4)) + 64 / (ε / 4) ^ 2 ≤
      (firstWidth m ε : ℝ) := Nat.le_ceil _

theorem gaussian_firstWidth_pos (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    0 < firstWidth m ε := by
  have hr : (0 : ℝ) < rootWidth m := Nat.cast_pos.mpr (Counts.rootWidth_pos m)
  have hL : (0 : ℝ) ≤ logWidth m := Nat.cast_nonneg _
  have hη : 0 < ε / 4 := by positivity
  have hl := gaussian_firstWidth_lower m ε
  have hp : 0 < (firstWidth m ε : ℝ) := lt_of_lt_of_le (by positivity) hl
  exact_mod_cast hp

theorem gaussian_firstWidth_exponents (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    8 * (logWidth m : ℝ) ≤ (firstWidth m ε : ℝ) * (rootWidth m : ℝ) * (ε / 4) / 4 ∧
    8 ≤ (firstWidth m ε : ℝ) * (ε / 4) ^ 2 / 8 := by
  have hr : (0 : ℝ) < rootWidth m := Nat.cast_pos.mpr (Counts.rootWidth_pos m)
  have hη : 0 < ε / 4 := by positivity
  have hηsq : 0 < (ε / 4) ^ 2 := sq_pos_of_pos hη
  have hl := gaussian_firstWidth_lower m ε
  have h1 : 32 * (logWidth m : ℝ) / ((rootWidth m : ℝ) * (ε / 4)) ≤
      (firstWidth m ε : ℝ) := by
    have : 0 ≤ 64 / (ε / 4) ^ 2 := by positivity
    linarith
  have h2 : 64 / (ε / 4) ^ 2 ≤ (firstWidth m ε : ℝ) := by
    have : 0 ≤ 32 * (logWidth m : ℝ) / ((rootWidth m : ℝ) * (ε / 4)) := by positivity
    linarith
  have h1' := (div_le_iff₀ (mul_pos hr hη)).mp h1
  have h2' := (div_le_iff₀ hηsq).mp h2
  constructor <;> nlinarith

theorem gaussian_warm_failure_budget (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (m + 2 : ℝ) * Real.exp (-(firstWidth m ε : ℝ) * (rootWidth m : ℝ) * (ε / 4) / 4) +
        Real.exp (-(firstWidth m ε : ℝ) * (ε / 4) ^ 2 / 8) ≤
      2 * Real.exp (-16) + Real.exp (-8) := by
  have h := gaussian_firstWidth_exponents m ε hε
  have hlow : Real.exp (-(firstWidth m ε : ℝ) * (rootWidth m : ℝ) * (ε / 4) / 4) ≤
      Real.exp (-8 * (logWidth m : ℝ)) := Real.exp_le_exp.mpr (by linarith [h.1])
  have hupp : Real.exp (-(firstWidth m ε : ℝ) * (ε / 4) ^ 2 / 8) ≤ Real.exp (-8) :=
    Real.exp_le_exp.mpr (by linarith [h.2])
  exact add_le_add ((mul_le_mul_of_nonneg_left hlow (by positivity)).trans
    (gaussian_size_exp_bound m)) hupp

/-- The source's literal warm-start event with its explicit failure budget. -/
theorem sketchWarmIndex_explicit_tail_bound {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε0 : 0 < ε) (hεh : ε < 1 / 2)
    (hsketch : firstWidth m ε + secondWidth m ε + thirdWidth m ε < n) :
    GaussianLaw.real {ω | ((1 + ε / 4) / (1 - ε / 4)) * (optimum A F) ^ 2 <
      residualTailEnergy (A - F (sketchWarmIndex F A (makePlan n m ε ω))) (rootWidth m)} ≤
      2 * Real.exp (-16) + Real.exp (-8) := by
  have hr : rootWidth m < n := by
    have hk : rootWidth m < secondWidth m ε := by dsimp [secondWidth]; omega
    omega
  exact (sketchWarmIndex_tail_bound F A ε hsketch (gaussian_firstWidth_pos m ε hε0)
    (rootWidth m) hr (ε / 4) (by positivity) (by linarith)).trans
      (gaussian_warm_failure_budget m ε hε0)

/-- A kernel-proved rational margin for the final union of failure budgets. -/
theorem gaussian_total_failure_budget_lt :
    Real.exp (-8) + 2 * Real.exp (-16) + (1 / 128 : ℝ) + 1 / 524288 < 1 / 100 := by
  have h8 : (2000 : ℝ) < Real.exp 8 := by
    calc
      (2000 : ℝ) < (27 / 10 : ℝ) ^ 8 := by norm_num
      _ < (Real.exp 1) ^ 8 := by gcongr; linarith [Real.exp_one_gt_d9]
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hx : Real.exp (-8) < (1 / 2000 : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) h8
  have hx0 : 0 ≤ Real.exp (-8) := (Real.exp_pos _).le
  have hx2 : (Real.exp (-8)) ^ 2 < (1 / 2000 : ℝ) ^ 2 := by gcongr
  have he : Real.exp (-16) = (Real.exp (-8)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  rw [he]
  nlinarith

#assert_trust kernel gaussian_logWidth_ge_two
#assert_trust kernel gaussian_size_exp_bound
#assert_trust kernel gaussian_firstWidth_lower
#assert_trust kernel gaussian_firstWidth_pos
#assert_trust kernel gaussian_firstWidth_exponents
#assert_trust kernel gaussian_warm_failure_budget
#assert_trust kernel sketchWarmIndex_explicit_tail_bound
#assert_trust kernel gaussian_total_failure_budget_lt
#print axioms gaussian_logWidth_ge_two
#print axioms gaussian_size_exp_bound
#print axioms gaussian_firstWidth_lower
#print axioms gaussian_firstWidth_pos
#print axioms gaussian_firstWidth_exponents
#print axioms gaussian_warm_failure_budget
#print axioms sketchWarmIndex_explicit_tail_bound
#print axioms gaussian_total_failure_budget_lt
end NLA.Proofs.RE06
