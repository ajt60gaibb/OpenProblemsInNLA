/-
Copyright (c) 2026 Arav Bhattacharyya.
Released under Apache 2.0 license. Implemented with OpenAI Codex assistance.
The imported Komlós proof is by Gabriel Dahia, following Karingula and Lovett.
-/
import NLA.Statements.MD03
import Komlos.Main

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.MD03

/-- Translate the external discrepancy definition to explicit signs and row sums. -/
theorem signing {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : ∀ j, ∑ i, (A i j) ^ 2 ≤ 1) :
    ∃ x : Fin n → ℝ, (∀ j, x j = -1 ∨ x j = 1) ∧
      ∀ i, |∑ j, A i j * x j| ≤ 36 := by
  obtain ⟨x, hx, hbound⟩ := Komlos.discrepancy_le_iff.mp
    (Komlos.discrepancy_le_of_forall_sum_sq_le_one A hA)
  exact ⟨x, fun j ↦ (hx j).symm,
    (Komlos.colouringDiscrepancy_le_iff (by norm_num)).mp hbound⟩

/-- The complete, unchanged reviewed MD-03 target, with witness C = 36. -/
theorem target : NLA.Statements.MD03.Target := by
  refine ⟨36, by norm_num, ?_⟩
  intro m n _hm _hn A hA
  exact signing A hA

#assert_trust kernel target
#print axioms target

end NLA.MD03
