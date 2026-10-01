import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

/-!
# Logarithmic removal budgets for the finite separator argument

A single explicitly chosen initial segment makes the doubly exponential error
at most `1/m`. Its size is logarithmic in `m`, uniformly before the finite family
is chosen. The logarithm is then absorbed into any fixed positive power.
-/

noncomputable section

namespace ProofProject

def separatorRemovalIndex (c T : ℝ) (m : ℕ) : ℕ :=
  Nat.ceil ((3 / c) * Real.log (max 1 T * (m : ℝ)))

/-- Bernoulli's inequality supplies the linear growth needed by the explicit
ceiling construction; no asymptotic choice of index is used. -/
theorem separator_base_pow_lower (J : ℕ) :
    1 + (J : ℝ) / 3 ≤ (4 / 3 : ℝ) ^ J := by
  calc
    _ = 1 + (J : ℝ) * (1 / 3) := by ring
    _ ≤ (1 + (1 / 3 : ℝ)) ^ J := one_add_mul_le_pow (by norm_num) J
    _ = _ := by norm_num

/-- The explicit initial segment meets the reciprocal finite-family budget. -/
theorem separatorRemovalIndex_budget {c T : ℝ} (hc : 0 < c)
    (m : ℕ) (hm : 1 ≤ m) :
    T * Real.exp (-c * (4 / 3 : ℝ) ^ separatorRemovalIndex c T m) ≤ 1 / (m : ℝ) := by
  let D : ℝ := max 1 T
  let J := separatorRemovalIndex c T m
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  have hj : 3 * Real.log (D * (m : ℝ)) / c ≤ (J : ℝ) := by
    have h := Nat.le_ceil ((3 / c) * Real.log (D * (m : ℝ)))
    change (3 / c) * Real.log (D * (m : ℝ)) ≤ (J : ℝ) at h
    convert h using 1 <;> ring
  have hj' := (div_le_iff₀ hc).mp hj
  have hp := mul_le_mul_of_nonneg_left (separator_base_pow_lower J) hc.le
  have hlog : Real.log (D * (m : ℝ)) ≤ c * (4 / 3 : ℝ) ^ J := by nlinarith
  have he : Real.exp (-c * (4 / 3 : ℝ) ^ J) ≤ (D * (m : ℝ))⁻¹ := by
    calc
      _ ≤ Real.exp (-Real.log (D * (m : ℝ))) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (mul_pos hD hm0)]
  calc
    _ ≤ D * Real.exp (-c * (4 / 3 : ℝ) ^ J) :=
      mul_le_mul_of_nonneg_right (le_max_right 1 T) (Real.exp_pos _).le
    _ ≤ D * (D * (m : ℝ))⁻¹ := mul_le_mul_of_nonneg_left he hD.le
    _ = _ := by field_simp [hD.ne', hm0.ne']

/-- The size constant depends only on the fixed scalar error parameters, and
is chosen before every positive finite-family size. -/
theorem exists_separatorRemovalIndex_log_bound {c T : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      (separatorRemovalIndex c T m : ℝ) ≤ C * Real.log ((m : ℝ) + 2) := by
  let D : ℝ := max 1 T
  let K : ℝ := 3 / c
  let B : ℝ := K * Real.log D + 1
  let C : ℝ := K + B / Real.log 3
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hK : 0 < K := by dsimp [K]; positivity
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hB : 0 < B := by dsimp [B]; positivity
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro m hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  have hDm : 1 ≤ D * (m : ℝ) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ D * (m : ℝ) := mul_le_mul hD1 hm1 (by norm_num) hD.le
  have harg : 0 ≤ K * Real.log (D * (m : ℝ)) :=
    mul_nonneg hK.le (Real.log_nonneg hDm)
  have hceil : (separatorRemovalIndex c T m : ℝ) ≤ K * Real.log (D * (m : ℝ)) + 1 :=
    (Nat.ceil_lt_add_one harg).le
  have hlogm : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_le_log hm0 (by linarith)
  have hloglower : Real.log 3 ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hBbound : B ≤ (B / Real.log 3) * Real.log ((m : ℝ) + 2) := by
    have h := mul_le_mul_of_nonneg_left hloglower (div_nonneg hB.le hlog3.le)
    have heq : (B / Real.log 3) * Real.log 3 = B := by field_simp [hlog3.ne']
    rwa [heq] at h
  calc
    _ ≤ K * Real.log (D * (m : ℝ)) + 1 := hceil
    _ = K * Real.log (m : ℝ) + B := by rw [Real.log_mul hD.ne' hm0.ne']; dsimp [B]; ring
    _ ≤ K * Real.log ((m : ℝ) + 2) + B :=
      add_le_add (mul_le_mul_of_nonneg_left hlogm hK.le) le_rfl
    _ ≤ K * Real.log ((m : ℝ) + 2) + (B / Real.log 3) * Real.log ((m : ℝ) + 2) :=
      add_le_add le_rfl hBbound
    _ = _ := by dsimp [C]; ring

/-- Uniform removal budget in the form needed by the finite operator assembly. -/
theorem exists_separatorRemoval_budget {c T : ℝ} (hc : 0 < c) (_hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∃ J : ℕ,
      (J : ℝ) ≤ C * Real.log ((m : ℝ) + 2) ∧
      T * Real.exp (-c * (4 / 3 : ℝ) ^ J) ≤ 1 / (m : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_separatorRemovalIndex_log_bound (T := T) hc
  exact ⟨C, hC, fun m hm => ⟨separatorRemovalIndex c T m, hbound m hm,
    separatorRemovalIndex_budget hc m hm⟩⟩

/-- Explicit absorption of the removed logarithmic segment into a positive
power, uniformly from `m = 1`. -/
theorem log_add_two_le_rpow {α : ℝ} (hα : 0 < α) (m : ℕ) (hm : 1 ≤ m) :
    Real.log ((m : ℝ) + 2) ≤ ((3 : ℝ) ^ α / α) * (m : ℝ) ^ α := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  calc
    _ ≤ ((m : ℝ) + 2) ^ α / α := Real.log_le_rpow_div (by positivity) hα
    _ ≤ (3 * (m : ℝ)) ^ α / α := div_le_div_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) (by linarith) hα.le) hα.le
    _ = _ := by rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)]; ring

theorem exists_log_add_two_le_rpow {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      Real.log ((m : ℝ) + 2) ≤ C * (m : ℝ) ^ α :=
  ⟨(3 : ℝ) ^ α / α, div_pos (Real.rpow_pos_of_pos (by norm_num) _) hα,
    log_add_two_le_rpow hα⟩

end ProofProject
