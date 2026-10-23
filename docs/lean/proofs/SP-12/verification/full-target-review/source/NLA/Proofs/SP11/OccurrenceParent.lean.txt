import NLA.Proofs.SP11.LSSLabelBounds

/-!
# Parents of actual finite-tree occurrences

Every occurrence below the root is the child output of an actual parent node.
The statement preserves its entire dependent outer path; no abstract parent
oracle is supplied to the later coloring argument.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11.GardenTree

variable {V : Type*} {arity : V → ℕ}

theorem isRootOccurrence_iff_eq (t : GardenTree V arity) (o : Occurrence t) :
    IsRootOccurrence t o ↔ o = rootOccurrence t := by
  cases t with
  | node v children =>
    cases o with
    | inl u =>
      constructor
      · intro _
        apply congrArg Sum.inl
        exact Subsingleton.elim _ _
      · intro _
        trivial
    | inr o => simp [IsRootOccurrence, rootOccurrence]

/-- Every nonroot output conduit has an actual parent and one child slot. -/
theorem exists_parent_of_not_root (t : GardenTree V arity) (o : Occurrence t)
    (ho : ¬ IsRootOccurrence t o) :
    ∃ p : Occurrence t, ∃ s : Fin (arity (occurrenceLabel t p)),
      childOccurrence t p s = o := by
  classical
  induction t with
  | node v children ih =>
    cases o with
    | inl _u => exact False.elim (ho trivial)
    | inr so =>
      rcases so with ⟨s, o⟩
      by_cases hroot : IsRootOccurrence (children s) o
      · have heq := (isRootOccurrence_iff_eq (children s) o).mp hroot
        refine ⟨.inl (), s, ?_⟩
        change (Sum.inr (Sigma.mk s (rootOccurrence (children s))) : Occurrence (.node v children)) =
          Sum.inr (Sigma.mk s o)
        rw [heq]
      · obtain ⟨p, r, hpr⟩ := ih s o hroot
        refine ⟨.inr ⟨s, p⟩, r, ?_⟩
        change (Sum.inr (Sigma.mk s (childOccurrence (children s) p r)) : Occurrence (.node v children)) =
          Sum.inr (Sigma.mk s o)
        exact congrArg (fun q => (Sum.inr (Sigma.mk s q) : Occurrence (.node v children))) hpr

#assert_trust kernel isRootOccurrence_iff_eq
#assert_trust kernel exists_parent_of_not_root
#print axioms exists_parent_of_not_root

end NLA.Proofs.SP11.GardenTree
