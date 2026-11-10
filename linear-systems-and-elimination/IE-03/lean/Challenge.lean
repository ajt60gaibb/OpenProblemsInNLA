import NLA.IE03.Definitions

/-! The public statement lives in this independent challenge environment. -/

namespace NLA.IE03

/-- A real Hadamard matrix of order 4096 has a complete-pivoting path with
element-growth factor 4608. Sign entries make the initial maximum equal to one. -/
theorem counterexample : ∃ A : Entries ℝ, IsHadamard 4096 A ∧ CompletePath 4096 A 4608 := by
  sorry

/-- Cryer's assertion quantifies over every positive order, real Hadamard
matrix and admissible complete-pivoting path. -/
theorem cryer_false :
    ¬ (∀ (n : ℕ) (A : Entries ℝ) (g : ℝ),
      0 < n → IsHadamard n A → CompletePath n A g → g = (n : ℝ)) := by
  sorry

end NLA.IE03
