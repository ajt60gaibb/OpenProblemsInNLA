import Solution

example (m n : ℕ) (hm : 5 ≤ m) (hodd : Odd m) (hn : 2 ≤ n) :
    ∃ p : MvPolynomial (Fin (m * (n - 1) + 1)) ℂ,
      p ≠ 0 ∧ (NLA.TR13.principalOpen p).Nonempty ∧
      ∀ h ∈ NLA.TR13.principalOpen p,
        NLA.TR13.AllRanksEqual (NLA.TR13.hankel h) (NLA.TR13.expectedRank m n) :=
  NLA.TR13.generic_rank_equality m n hm hodd hn

#print axioms NLA.TR13.generic_rank_equality
#print axioms NLA.TR13.generic_border_lower
#print axioms NLA.TR13.all_ranks_equal_of_bounds
