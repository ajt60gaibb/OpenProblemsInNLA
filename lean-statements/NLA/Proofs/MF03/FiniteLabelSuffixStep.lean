import NLA.Proofs.MF03.FiniteColumnSystem

/-!
Exact arithmetic of zero-based finite factor-label cuts. This is the
recurrence used when a column system is reconstructed as a literal chain
of stationary or one-step path moves in descending label order.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- At cut zero, every finite label is included. -/
theorem finiteLabelSuffix_zero (S : Finset ℕ) :
    finiteLabelSuffix S 0 = S.card := by
  simp [finiteLabelSuffix]

/-- No label below `N` survives cut `N`. -/
theorem finiteLabelSuffix_top (N : ℕ) (S : Finset ℕ)
    (hbound : ∀ k ∈ S, k < N) :
    finiteLabelSuffix S N = 0 := by
  unfold finiteLabelSuffix
  apply Finset.card_eq_zero.mpr
  ext k
  constructor
  · intro hk
    have hmem := (Finset.mem_filter.mp hk).1
    have hge := (Finset.mem_filter.mp hk).2
    exact False.elim (by have := hbound k hmem; omega)
  · intro hk
    simp at hk

/-- Crossing factor label `q` adds exactly one to a suffix count if and
only if that label belongs to the finite column. -/
theorem finiteLabelSuffix_step (S : Finset ℕ) (q : ℕ) :
    finiteLabelSuffix S q = finiteLabelSuffix S (q + 1) +
      (if q ∈ S then 1 else 0) := by
  by_cases hq : q ∈ S
  · have hfilter : S.filter (fun k => q ≤ k) =
        insert q (S.filter (fun k => q + 1 ≤ k)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · intro hk
        by_cases heq : k = q
        · exact Or.inl heq
        · exact Or.inr ⟨hk.1, by omega⟩
      · intro hk
        rcases hk with heq | ⟨hmem, hge⟩
        · subst k
          exact ⟨hq, le_rfl⟩
        · exact ⟨hmem, by omega⟩
    simp [finiteLabelSuffix, hq, hfilter]
  · have hfilter : S.filter (fun k => q ≤ k) =
        S.filter (fun k => q + 1 ≤ k) := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · intro hk
        have hne : k ≠ q := by
          intro heq
          subst k
          exact hq hk.1
        exact ⟨hk.1, by omega⟩
      · intro hk
        exact ⟨hk.1, by omega⟩
    simp [finiteLabelSuffix, hq, hfilter]

#assert_trust kernel finiteLabelSuffix_step
#print axioms finiteLabelSuffix_step

end NLA.Proofs.MF03
