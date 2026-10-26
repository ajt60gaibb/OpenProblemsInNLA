import NLA.Proofs.SP11.CanonicalPair
import NLA.Proofs.SP11.OccurrenceParent

/-!
# Exact canonical colors at every actual occurrence

The normal coloring assigns each input its zero-based slot. Only the later
top root has the cap inserted among those slots; below it the rule is normal.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11.GardenTree

variable {V : Type*} {arity : V → ℕ} {d : ℕ}

/-- Every ordinary input conduit has exactly its local zero-based slot color. -/
theorem normalColoring_input_val (t : GardenTree V arity) (h : ArityBound d t)
    (q : Fin d) (o : Occurrence t) (s : Fin (arity (occurrenceLabel t o))) :
    (occurrenceColors t (normalColoring t h q) o s.succ).val = s.val := by
  induction t generalizing q with
  | node v children ih =>
    cases o with
    | inl _ =>
      change (rootColor (normalColoring (children s) (h.2 s)
        ⟨s.val, lt_trans s.isLt h.1⟩)).val = s.val
      rw [rootColor_normalColoring]
    | inr o =>
      rcases o with ⟨r, o⟩
      exact ih r (h.2 r) ⟨r.val, lt_trans r.isLt h.1⟩ o s

/-- Equivalent output-conduit version, with the actual child-occurrence map. -/
theorem normalColoring_child_output_val (t : GardenTree V arity) (h : ArityBound d t)
    (q : Fin d) (o : Occurrence t) (s : Fin (arity (occurrenceLabel t o))) :
    (occurrenceColors t (normalColoring t h q) (childOccurrence t o s) 0).val = s.val := by
  rw [← occurrenceColors_childOccurrence]
  exact normalColoring_input_val t h q o s

theorem rootOccurrence_arity_eq (t : GardenTree V arity) :
    arity (occurrenceLabel t (rootOccurrence t)) = rootArity t := by
  cases t
  rfl

/-- The later top-root inputs skip exactly the one common-cap position. The
cast changes only the proven equality of the root's arity descriptions. -/
theorem insertedColoring_root_input_val (t : GardenTree V arity) (h : ArityBound d t)
    (p : Fin (rootArity t + 1)) (s : Fin (rootArity t)) :
    (occurrenceColors t (insertedColoring t h p) (rootOccurrence t)
      (Fin.cast (rootOccurrence_arity_eq t).symm s).succ).val = (p.succAbove s).val := by
  cases t with
  | node v children =>
    change (rootColor (normalColoring (children s) (h.2 s)
      (Fin.castLE (Nat.succ_le_of_lt h.1) (p.succAbove s)))).val = _
    rw [rootColor_normalColoring]
    rfl

/-- Every input below the later top root retains the ordinary slot-color rule. -/
theorem insertedColoring_input_val_of_not_root (t : GardenTree V arity)
    (h : ArityBound d t) (p : Fin (rootArity t + 1))
    (o : Occurrence t) (ho : ¬ IsRootOccurrence t o)
    (s : Fin (arity (occurrenceLabel t o))) :
    (occurrenceColors t (insertedColoring t h p) o s.succ).val = s.val := by
  cases t with
  | node v children =>
    cases o with
    | inl _ => exact False.elim (ho trivial)
    | inr o =>
      rcases o with ⟨r, o⟩
      exact normalColoring_input_val (children r) (h.2 r)
        (Fin.castLE (Nat.succ_le_of_lt h.1) (p.succAbove r)) o s

#assert_trust kernel normalColoring_child_output_val
#assert_trust kernel insertedColoring_root_input_val
#assert_trust kernel insertedColoring_input_val_of_not_root
#print axioms normalColoring_child_output_val
#print axioms insertedColoring_input_val_of_not_root

end NLA.Proofs.SP11.GardenTree
