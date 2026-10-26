import NLA.Proofs.SP11.OccurrenceParent

/-!
# Earlier siblings block every smaller canonical color

The ordered-sibling lemma applies to an actual parent or to the later top
root with its cap inserted. The tree specialization uses the literal child
occurrence map and the parent's injective incident-color tuple.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11

/-- In an ordered sibling list whose canonical outputs are its slot indices,
every smaller canonical color has an earlier-label, distinct actual output. -/
theorem ordered_sibling_blockers {O : Type*} {n k : ℕ}
    (label : O → Fin n) (siblings : Fin k → O)
    (hlabel : StrictMono (fun s => label (siblings s)))
    (best actual : O → ℕ)
    (hbest : ∀ s : Fin k, best (siblings s) = s.val)
    (hinj : Function.Injective (fun s => actual (siblings s))) (s : Fin k) :
    ∀ q : ℕ, q < best (siblings s) →
      ∃ p, label p < label (siblings s) ∧ best p = q ∧
        actual (siblings s) ≠ actual p := by
  intro q hq
  rw [hbest] at hq
  let r : Fin k := ⟨q, lt_trans hq s.isLt⟩
  refine ⟨siblings r, hlabel (show r < s from hq), hbest r, ?_⟩
  intro heq
  have hrs : s = r := hinj heq
  have := congrArg Fin.val hrs
  change s.val = q at this
  omega

namespace GardenTree

variable {V : Type*} {arity : V → ℕ} {d n : ℕ}

/-- Distinct child slots are distinct outputs whenever the actual parent
tensor has injective incident colors. -/
theorem child_output_injective (t : GardenTree V arity) (c : Coloring d t)
    (p : Occurrence t) (hinj : Function.Injective (occurrenceColors t c p)) :
    Function.Injective (fun s : Fin (arity (occurrenceLabel t p)) =>
      (occurrenceColors t c (childOccurrence t p s) 0).val) := by
  intro s r heq
  have hc : occurrenceColors t c p s.succ = occurrenceColors t c p r.succ := by
    rw [occurrenceColors_childOccurrence, occurrenceColors_childOccurrence]
    exact Fin.ext heq
  exact Fin.succ_injective _ (hinj hc)

/-- Actual ordered child occurrences supply the blocker clause from a normal
canonical parent, preserving the full outer path of each occurrence. -/
theorem child_occurrence_blockers {a : Fin n → ℕ} (t : GardenTree (Fin n) a)
    (f : (v : Fin n) → Fin (a v) → Fin n)
    (ht : HasChildLabels f t) (hf : ∀ v, StrictMono (f v))
    (best actual : Coloring d t) (p : Occurrence t)
    (hbest : ∀ s : Fin (a (occurrenceLabel t p)),
      (occurrenceColors t best (childOccurrence t p s) 0).val = s.val)
    (hinj : Function.Injective (occurrenceColors t actual p))
    (s : Fin (a (occurrenceLabel t p))) :
    ∀ q : ℕ, q < (occurrenceColors t best (childOccurrence t p s) 0).val →
      ∃ o, occurrenceLabel t o < occurrenceLabel t (childOccurrence t p s) ∧
        (occurrenceColors t best o 0).val = q ∧
        (occurrenceColors t actual (childOccurrence t p s) 0).val ≠
          (occurrenceColors t actual o 0).val := by
  apply ordered_sibling_blockers (occurrenceLabel t) (childOccurrence t p)
    (best := fun o => (occurrenceColors t best o 0).val)
    (actual := fun o => (occurrenceColors t actual o 0).val)
  · intro r s hrs
    change occurrenceLabel t (childOccurrence t p r) <
      occurrenceLabel t (childOccurrence t p s)
    rw [occurrenceLabel_childOccurrence f t ht, occurrenceLabel_childOccurrence f t ht]
    exact hf (occurrenceLabel t p) hrs
  · exact hbest
  · exact child_output_injective t actual p hinj

end GardenTree

#assert_trust kernel ordered_sibling_blockers
#assert_trust kernel GardenTree.child_output_injective
#assert_trust kernel GardenTree.child_occurrence_blockers
#print axioms GardenTree.child_occurrence_blockers

end NLA.Proofs.SP11
