import NLA.TR13.Definitions

namespace NLA.TR13

/-- The complete original TR-13 assertion, with an explicit principal open set
and the stronger exact value of all five ranks. This declaration is trusted only
as the comparison boundary, never imported by a solution. -/
theorem generic_rank_equality (m n : ℕ) (hm : 5 ≤ m) (hodd : Odd m) (hn : 2 ≤ n) :
    ∃ p : MvPolynomial (Fin (m * (n - 1) + 1)) ℂ,
      p ≠ 0 ∧ (principalOpen p).Nonempty ∧
      ∀ h ∈ principalOpen p, AllRanksEqual (hankel h) (expectedRank m n) := by
  sorry

end NLA.TR13
