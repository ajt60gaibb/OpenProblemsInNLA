/-
Copyright (c) 2026 Arav Bhattacharyya.
Released under Apache 2.0 license. Implemented with OpenAI Codex assistance.
-/
import NLA.Statements.MD03
import NLA.Statements.MD04
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.MD04

/-- Komlós implies the reviewed Beck–Fiala target, with the same constant.
This reduction uses only the two elementary statements and mathlib. -/
theorem of_komlos (hKomlos : NLA.Statements.MD03.Target) :
    NLA.Statements.MD04.Target := by
  obtain ⟨C, hC, hKomlos⟩ := hKomlos
  refine ⟨C, hC, ?_⟩
  intro m n t hm hn ht _htm A h01 hcol
  have htpos : (0 : ℝ) < t := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
  have hspos : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htpos
  have hsne : Real.sqrt (t : ℝ) ≠ 0 := ne_of_gt hspos
  let B : Matrix (Fin m) (Fin n) ℝ := fun i j ↦ A i j / Real.sqrt (t : ℝ)
  have hB : ∀ j, ∑ i, (B i j) ^ 2 ≤ 1 := by
    intro j
    calc
      ∑ i, (B i j) ^ 2 = (∑ i, A i j) / (t : ℝ) := by
        simp only [B, div_pow, Real.sq_sqrt (le_of_lt htpos)]
        rw [← Finset.sum_div]
        congr 1
        apply Finset.sum_congr rfl
        intro i _hi
        rcases h01 i j with h | h <;> simp [h]
      _ ≤ 1 := (div_le_one htpos).mpr (hcol j)
  obtain ⟨x, hx, hbound⟩ := hKomlos m n hm hn B hB
  refine ⟨x, hx, ?_⟩
  intro i
  have hsum : (∑ j, B i j * x j) * Real.sqrt (t : ℝ) =
      ∑ j, A i j * x j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _hj
    dsimp [B]
    field_simp
  calc
    |∑ j, A i j * x j| = |∑ j, B i j * x j| * Real.sqrt (t : ℝ) := by
      rw [← hsum, abs_mul, abs_of_pos hspos]
    _ ≤ C * Real.sqrt (t : ℝ) :=
      mul_le_mul_of_nonneg_right (hbound i) (le_of_lt hspos)

end NLA.MD04
