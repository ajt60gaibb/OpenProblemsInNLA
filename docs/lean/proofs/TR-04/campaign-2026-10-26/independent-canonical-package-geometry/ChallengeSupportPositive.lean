import FullChallenge
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace IndependentCanonicalChallengeGeometry

theorem literal_count {n₁ t k : ℕ} (ht : t≤n₁) (hk : k≤t) : k≤n₁ :=
  candidate_count_le_first_mode ht hk

theorem literal_cyclic {n₁ t : ℕ} (ht : t≤n₁) : t≤n₁ :=
  cyclic_window_count_le_first_mode ht

#assert_trust kernel candidate_count_le_first_mode
#assert_trust kernel cyclic_window_count_le_first_mode
#assert_trust kernel literal_count
#assert_trust kernel literal_cyclic
#print axioms candidate_count_le_first_mode
#print axioms cyclic_window_count_le_first_mode
#print axioms literal_count
#print axioms literal_cyclic
end IndependentCanonicalChallengeGeometry
