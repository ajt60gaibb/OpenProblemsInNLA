import NLA.KE03.Correctness

namespace NLA.KE03

/-- KE-03 in full: one terminating randomized exact-query algorithm, with
joint success probability at least 0.99, for every permitted matrix and input. -/
theorem complete_query_algorithm : ∃ C : ℝ, 0 < C ∧ SolvesKE03 C := by
  exact ⟨32768, by norm_num, solvesKE03⟩

end NLA.KE03
