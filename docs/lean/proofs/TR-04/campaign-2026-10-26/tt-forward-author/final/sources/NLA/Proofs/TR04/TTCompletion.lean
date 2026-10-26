import NLA.Proofs.TR04.TensorCompressionSVD

/-! A concrete recursive TT-SVD response relation, permitting every tuple
satisfying the unchanged machine SVD contract. No approximation or feasibility
claim is built into this relation; those properties are proved separately. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine

/-- Requested ranks are indexed by the cuts after one, two, ... modes. -/
def RankFeasible (ns : List ℕ) (r : ℕ → ℕ) (A : Tensor ns) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j < ns.length → Matrix.rank (unfold ns A j) ≤ r (j - 1)

def stepRank (m : ℕ) (ns : List ℕ) (r : ℕ → ℕ) : ℕ :=
  cappedRank m (suffixSize ns) (r 0)

def stepFrame {m : ℕ} (ns : List ℕ) (r : ℕ → ℕ)
    (U : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin (stepRank m ns r)) ℝ :=
  prefixFrame (l := suffixSize ns) U (r 0)

def stepInput {m n : ℕ} {ns : List ℕ} (r : ℕ → ℕ)
    (U : Matrix (Fin m) (Fin m) ℝ) (A : Tensor (m :: n :: ns)) :
    Tensor ((stepRank m (n :: ns) r * n) :: ns) :=
  merge (stepRank m (n :: ns) r) n ns (contract (stepFrame (n :: ns) r U) A)

def stepOutput {m n : ℕ} {ns : List ℕ} (r : ℕ → ℕ)
    (U : Matrix (Fin m) (Fin m) ℝ)
    (Z : Tensor ((stepRank m (n :: ns) r * n) :: ns)) : Tensor (m :: n :: ns) :=
  lift (stepFrame (n :: ns) r U) ((merge (stepRank m (n :: ns) r) n ns).symm Z)

/-- Every recursive choice is an actual valid SVD of the current dense first
unfolding. Empty/single-mode formats terminate exactly. -/
inductive Completion : (ns : List ℕ) → (r : ℕ → ℕ) → Tensor ns → Tensor ns → Prop
  | nil (r : ℕ → ℕ) (A : Tensor []) : Completion [] r A A
  | single (m : ℕ) (r : ℕ → ℕ) (A : Tensor [m]) : Completion [m] r A A
  | step {m n : ℕ} {ns : List ℕ} {r : ℕ → ℕ} {A : Tensor (m :: n :: ns)}
      {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize (n :: ns))) → ℝ}
      {V : Matrix (Fin (suffixSize (n :: ns))) (Fin (suffixSize (n :: ns))) ℝ}
      (hSVD : ValidSVD (denseFirst A) U sigma V)
      {Z : Tensor ((stepRank m (n :: ns) r * n) :: ns)}
      (hchild : Completion ((stepRank m (n :: ns) r * n) :: ns) (fun j => r (j + 1))
        (stepInput r U A) Z) :
      Completion (m :: n :: ns) r A (stepOutput r U Z)

/-- The recursive operation is total on all finite formats and rank bounds. -/
theorem completion_exists (ns : List ℕ) (r : ℕ → ℕ) (A : Tensor ns) :
    ∃ X : Tensor ns, Completion ns r A X := by
  classical
  have H : ∀ d : ℕ, ∀ ns : List ℕ, ns.length = d → ∀ r : ℕ → ℕ,
      ∀ A : Tensor ns, ∃ X : Tensor ns, Completion ns r A X := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro ns hlen r A
      cases ns with
      | nil => exact ⟨A, Completion.nil r A⟩
      | cons m rest =>
        cases rest with
        | nil => exact ⟨A, Completion.single m r A⟩
        | cons n ns =>
          obtain ⟨U, sigma, V, hSVD⟩ := SVD.exists_validSVD (denseFirst A)
          have hshort : ((stepRank m (n :: ns) r * n) :: ns).length < d := by
            simp only [List.length_cons] at hlen ⊢
            omega
          obtain ⟨Z, hZ⟩ := ih _ hshort _ rfl (fun j => r (j + 1)) (stepInput r U A)
          exact ⟨stepOutput r U Z, Completion.step hSVD hZ⟩
  exact H ns.length ns rfl r A

/-- An arbitrary chosen orthonormal compression preserves comparator ranks
at exactly the remaining cuts after merging. -/
theorem rankFeasible_merge_contract {m k n : ℕ} {ns : List ℕ} (r : ℕ → ℕ)
    (U : Matrix (Fin m) (Fin k) ℝ) {Y : Tensor (m :: n :: ns)}
    (hY : RankFeasible (m :: n :: ns) r Y) :
    RankFeasible ((k * n) :: ns) (fun j => r (j + 1))
      (merge k n ns (contract U Y)) := by
  intro j hj hlen
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
  rw [rank_unfold_merge]
  have hle := rank_unfold_contract_le U Y (t + 1)
  have hy := hY (t + 2) (by omega) (by simp only [List.length_cons] at hlen ⊢; omega)
  exact hle.trans (by simpa using hy)

/-- Every actual recursive response has all the requested unfolding ranks. -/
theorem completion_feasible {ns : List ℕ} {r : ℕ → ℕ} {A X : Tensor ns}
    (h : Completion ns r A X) : RankFeasible ns r X := by
  induction h with
  | nil r A => intro j hj hlen; simp at hlen
  | single m r A => intro j hj hlen; simp at hlen; omega
  | @step m n ns r A U sigma V hSVD Z hchild ih =>
    intro j hj hlen
    by_cases hfirst : j = 1
    · subst j
      have hbound := rank_unfold_lift_one_le (stepFrame (n :: ns) r U)
        ((merge (stepRank m (n :: ns) r) n ns).symm Z)
      exact hbound.trans (Nat.min_le_left _ _)
    · obtain ⟨t, rfl⟩ : ∃ t, j = t + 2 := ⟨j - 2, by omega⟩
      have hbound := rank_unfold_lift_le (stepFrame (n :: ns) r U)
        ((merge (stepRank m (n :: ns) r) n ns).symm Z) (t + 1)
      have hmerge := rank_unfold_merge (stepRank m (n :: ns) r) n ns
        ((merge (stepRank m (n :: ns) r) n ns).symm Z) t
      rw [LinearEquiv.apply_symm_apply] at hmerge
      have hi := ih (t + 1) (by omega) (by simp only [List.length_cons] at hlen ⊢; omega)
      exact hbound.trans (by rw [← hmerge]; simpa using hi)

#assert_trust kernel Completion
#assert_trust kernel completion_exists
#assert_trust kernel rankFeasible_merge_contract
#assert_trust kernel completion_feasible
#print axioms completion_exists
#print axioms completion_feasible
end NLA.Proofs.TR04.TensorFormat
