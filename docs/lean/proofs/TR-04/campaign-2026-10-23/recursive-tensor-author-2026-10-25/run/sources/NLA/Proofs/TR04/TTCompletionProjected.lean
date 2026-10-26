import NLA.Proofs.TR04.TTCompletionBound

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.Proofs.TR04.TensorFormat

/-- Arbitrary first frames, including cyclic tied-eigenspace frames, have all
requested ranks after an actual ordinary completion of their compressed input. -/
theorem projected_completion_feasible {m k n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    (U : Matrix (Fin m) (Fin k) ℝ) (hk : k ≤ r 0) (A : Tensor (m :: n :: ns))
    {Z : Tensor ((k * n) :: ns)}
    (hZ : Completion ((k * n) :: ns) (fun j => r (j + 1))
      (merge k n ns (contract U A)) Z) :
    RankFeasible (m :: n :: ns) r (lift U ((merge k n ns).symm Z)) := by
  have ih := completion_feasible hZ
  intro j hj hlen
  by_cases hfirst : j = 1
  · subst j
    exact (rank_unfold_lift_one_le U ((merge k n ns).symm Z)).trans hk
  · obtain ⟨t, rfl⟩ : ∃ t, j = t + 2 := ⟨j - 2, by omega⟩
    have hbound := rank_unfold_lift_le U ((merge k n ns).symm Z) (t + 1)
    have hmerge := rank_unfold_merge k n ns ((merge k n ns).symm Z) t
    rw [LinearEquiv.apply_symm_apply] at hmerge
    have hi := ih (t + 1) (by omega) (by simp only [List.length_cons] at hlen ⊢; omega)
    exact hbound.trans (by rw [← hmerge]; simpa using hi)

/-- A total actual completion, with one output that satisfies the strong
projected-comparator estimate simultaneously for all feasible comparators. -/
theorem exists_projected_completion {m k n : ℕ} (ns : List ℕ) (r : ℕ → ℕ)
    (U : Matrix (Fin m) (Fin k) ℝ) (hU : SVD.OrthonormalColumns U) (hk : k ≤ r 0)
    (A : Tensor (m :: n :: ns)) :
    ∃ Z : Tensor ((k * n) :: ns),
      Completion ((k * n) :: ns) (fun j => r (j + 1))
        (merge k n ns (contract U A)) Z ∧
      RankFeasible (m :: n :: ns) r (lift U ((merge k n ns).symm Z)) ∧
      ∀ Y : Tensor (m :: n :: ns), RankFeasible (m :: n :: ns) r Y →
        error (m :: n :: ns) A (lift U ((merge k n ns).symm Z)) ≤
          error (m :: n :: ns) A (lift U (contract U A)) +
            (ns.length : ℝ) * energy (m :: n :: ns) (lift U (contract U (A - Y))) := by
  obtain ⟨Z, hZ⟩ := completion_exists ((k * n) :: ns) (fun j => r (j + 1))
    (merge k n ns (contract U A))
  exact ⟨Z, hZ, projected_completion_feasible U hk A hZ,
    fun Y hY => projected_completion_bound hU A Y hY hZ⟩

#assert_trust kernel projected_completion_feasible
#assert_trust kernel exists_projected_completion
#print axioms exists_projected_completion
end NLA.Proofs.TR04.TensorFormat
