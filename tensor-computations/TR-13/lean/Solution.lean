import NLA.TR13.Upper
import NLA.TR13.Lower
import NLA.TR13.RankComparison
import NLA.TR13.ExactStatementBridge

namespace NLA.TR13

/-- Complete TR-13: a nonempty principal Zariski-open subset of every
admissible complex Hankel parameter space has all five ranks equal. -/
theorem generic_rank_equality (m n : ℕ) (hm : 5 ≤ m) (hodd : Odd m) (hn : 2 ≤ n) :
    ∃ p : MvPolynomial (Fin (m * (n - 1) + 1)) ℂ,
      p ≠ 0 ∧ (principalOpen p).Nonempty ∧
      ∀ h ∈ principalOpen p, AllRanksEqual (hankel h) (expectedRank m n) := by
  obtain ⟨p, hp, hu⟩ := generic_vandermonde_upper m n hm hodd hn
  obtain ⟨q, hq, hl⟩ := generic_border_lower m n hm hodd hn
  refine ⟨p * q, mul_ne_zero hp hq, principalOpen_nonempty (mul_ne_zero hp hq), ?_⟩
  intro h hh
  change MvPolynomial.eval h (p * q) ≠ 0 at hh
  rw [map_mul] at hh
  obtain ⟨hph, hqh⟩ := mul_ne_zero_iff.mp hh
  exact all_ranks_equal_of_bounds (by omega) (hu h hph) (hl h hqh)

end NLA.TR13
