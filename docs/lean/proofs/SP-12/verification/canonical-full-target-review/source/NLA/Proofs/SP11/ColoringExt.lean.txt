import NLA.Proofs.SP11.DoubleHistogramWeights

/-!
# Exact coloring extensionality at actual node occurrences

Every conduit output is part of the finite coloring data. Recovering those
outputs recovers the actual summand index, not merely its histogram.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11.GardenTree

variable {V : Type*} {arity : V → ℕ} {d : ℕ}

/-- Equality of the output color at every actual occurrence determines a tree coloring. -/
theorem coloring_ext_of_occurrence_outputs (t : GardenTree V arity)
    (c c' : Coloring d t)
    (h : ∀ o : Occurrence t, occurrenceColors t c o 0 = occurrenceColors t c' o 0) :
    c = c' := by
  induction t with
  | node v children ih =>
    rcases c with ⟨q, cs⟩
    rcases c' with ⟨q', cs'⟩
    apply Prod.ext
    · exact h (.inl ())
    · funext s
      apply ih s (cs s) (cs' s)
      intro o
      exact h (.inr ⟨s, o⟩)

/-- Recovering all actual node outputs recovers the entire paired coloring,
including its one shared cap color and every choice below both roots. -/
theorem doubleColoring_ext_of_occurrence_outputs (t u : GardenTree V arity)
    (c c' : DoubleColoring d t u)
    (h : ∀ o : DoubleOccurrence t u,
      doubleOccurrenceColors t u c o 0 = doubleOccurrenceColors t u c' o 0) :
    c = c' := by
  have hl : leftColoring c = leftColoring c' :=
    coloring_ext_of_occurrence_outputs t _ _ (fun o => h (.inl o))
  have hr : rightColoring c = rightColoring c' :=
    coloring_ext_of_occurrence_outputs u _ _ (fun o => h (.inr o))
  cases t with
  | node v children =>
    cases u with
    | node w descendants =>
      change (c.1, c.2.1) = (c'.1, c'.2.1) at hl
      change (c.1, c.2.2) = (c'.1, c'.2.2) at hr
      obtain ⟨hq, hleft⟩ := Prod.mk.inj hl
      obtain ⟨_, hright⟩ := Prod.mk.inj hr
      exact Prod.ext hq (Prod.ext hleft hright)
#assert_trust kernel coloring_ext_of_occurrence_outputs
#assert_trust kernel doubleColoring_ext_of_occurrence_outputs
#print axioms doubleColoring_ext_of_occurrence_outputs

end NLA.Proofs.SP11.GardenTree
