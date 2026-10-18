import NLA.Proofs.SP11.DoubleRootGarden
import NLA.Proofs.SP11.PriorListStructure

/-!
# Strict labels in the actual LSS recursion trees

Every child has a strictly smaller original vertex label. Therefore every
descendant is below its parent root, and the root is the only occurrence of
its own label. The ordered and augmented sibling lists retain strict labels.
These are structural facts, not a noncancellation or faithfulness theorem.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11
namespace GardenTree

variable {V : Type*} {arity : V → ℕ}

def rootLabel : GardenTree V arity → V
  | .node v _ => v

def rootOccurrence : (t : GardenTree V arity) → Occurrence t
  | .node _ _ => .inl ()

@[simp] theorem occurrenceLabel_rootOccurrence (t : GardenTree V arity) :
    occurrenceLabel t (rootOccurrence t) = rootLabel t := by cases t; rfl

/-- The child edge at any actual occurrence, preserving its full outer path. -/
def childOccurrence : (t : GardenTree V arity) → (o : Occurrence t) →
    Fin (arity (occurrenceLabel t o)) → Occurrence t
  | .node _ children, .inl _, s => .inr ⟨s, rootOccurrence (children s)⟩
  | .node _ children, .inr ⟨r, o⟩, s =>
      .inr ⟨r, childOccurrence (children r) o s⟩

@[simp] theorem occurrenceColors_rootOccurrence {d : ℕ} (t : GardenTree V arity)
    (c : Coloring d t) : occurrenceColors t c (rootOccurrence t) 0 = rootColor c := by
  cases t
  rfl

/-- An input conduit and its child's output are one actual edge, with one color. -/
theorem occurrenceColors_childOccurrence {d : ℕ} (t : GardenTree V arity)
    (c : Coloring d t) (o : Occurrence t) (s : Fin (arity (occurrenceLabel t o))) :
    occurrenceColors t c o s.succ = occurrenceColors t c (childOccurrence t o s) 0 := by
  induction t with
  | node v children ih =>
    cases o with
    | inl _ => exact (occurrenceColors_rootOccurrence (children s) (c.2 s)).symm
    | inr o =>
      rcases o with ⟨r, o⟩
      exact ih r (c.2 r) o s

/-- Every child label is the specified label-indexed predecessor, recursively. -/
def HasChildLabels (f : (v : V) → Fin (arity v) → V) : GardenTree V arity → Prop
  | .node v children =>
      (∀ s, rootLabel (children s) = f v s) ∧ ∀ s, HasChildLabels f (children s)

theorem occurrenceLabel_childOccurrence
    (f : (v : V) → Fin (arity v) → V) (t : GardenTree V arity)
    (h : HasChildLabels f t) (o : Occurrence t)
    (s : Fin (arity (occurrenceLabel t o))) :
    occurrenceLabel t (childOccurrence t o s) = f (occurrenceLabel t o) s := by
  induction t with
  | node v children ih =>
    cases o with
    | inl _ =>
      change occurrenceLabel (children s) (rootOccurrence (children s)) = f v s
      rw [occurrenceLabel_rootOccurrence]
      exact h.1 s
    | inr o =>
      rcases o with ⟨r, o⟩
      exact ih r (h.2 r) o s

/-- The root occurrence is distinguished from all occurrences below a child. -/
def IsRootOccurrence : (t : GardenTree V arity) → Occurrence t → Prop
  | .node _ _, .inl _ => True
  | .node _ _, .inr _ => False

/-- Every immediate child-root label is strictly smaller, recursively. -/
def DescendingLabels [LT V] : GardenTree V arity → Prop
  | .node v children =>
      (∀ s, rootLabel (children s) < v) ∧ ∀ s, DescendingLabels (children s)

variable [Preorder V]

theorem occurrenceLabel_le_root (t : GardenTree V arity) (h : DescendingLabels t)
    (o : Occurrence t) : occurrenceLabel t o ≤ rootLabel t := by
  induction t with
  | node v children ih =>
    cases o with
    | inl _ => exact le_rfl
    | inr o =>
      rcases o with ⟨s, o⟩
      exact (ih s (h.2 s) o).trans (h.1 s).le

theorem occurrenceLabel_lt_root_of_not_root (t : GardenTree V arity)
    (h : DescendingLabels t) (o : Occurrence t) (ho : ¬ IsRootOccurrence t o) :
    occurrenceLabel t o < rootLabel t := by
  cases t with
  | node v children =>
    cases o with
    | inl _ => exact False.elim (ho trivial)
    | inr o =>
      rcases o with ⟨s, o⟩
      exact lt_of_le_of_lt (occurrenceLabel_le_root _ (h.2 s) o) (h.1 s)

/-- No proper descendant can carry its root's label. -/
theorem occurrenceLabel_eq_root_iff (t : GardenTree V arity)
    (h : DescendingLabels t) (o : Occurrence t) :
    occurrenceLabel t o = rootLabel t ↔ IsRootOccurrence t o := by
  constructor
  · intro heq
    by_contra ho
    have hlt := occurrenceLabel_lt_root_of_not_root t h o ho
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · intro ho
    cases t with
    | node v children =>
      cases o with
      | inl _ => rfl
      | inr _ => exact False.elim ho

end GardenTree

theorem lssGarden_rootLabel {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) :
    (lssGarden G j).rootLabel = j := by
  rw [lssGarden_eq]
  rfl

/-- All occurrences use their own original label's actual predecessor list. -/
theorem lssGarden_hasChildLabels {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) :
    GardenTree.HasChildLabels (priorVertex G) (lssGarden G j) := by
  induction j using (measure (fun j : Fin n => j.val)).wf.induction with
  | h j ih =>
    rw [lssGarden_eq]
    exact ⟨fun s => lssGarden_rootLabel G (priorVertex G j s),
      fun s => ih (priorVertex G j s) (priorVertex_lt G j s)⟩

theorem lssGarden_childOccurrence_label {n : ℕ} (G : SimpleGraph (Fin n))
    (j : Fin n) (o : GardenTree.Occurrence (lssGarden G j))
    (s : Fin (priorNonneighbors G (GardenTree.occurrenceLabel (lssGarden G j) o)).length) :
    GardenTree.occurrenceLabel (lssGarden G j)
        (GardenTree.childOccurrence (lssGarden G j) o s) =
      priorVertex G (GardenTree.occurrenceLabel (lssGarden G j) o) s :=
  GardenTree.occurrenceLabel_childOccurrence (priorVertex G) _ (lssGarden_hasChildLabels G j) o s

theorem lssGarden_childOccurrence_label_lt {n : ℕ} (G : SimpleGraph (Fin n))
    (j : Fin n) (o : GardenTree.Occurrence (lssGarden G j))
    (s : Fin (priorNonneighbors G (GardenTree.occurrenceLabel (lssGarden G j) o)).length) :
    GardenTree.occurrenceLabel (lssGarden G j)
        (GardenTree.childOccurrence (lssGarden G j) o s) <
      GardenTree.occurrenceLabel (lssGarden G j) o := by
  rw [lssGarden_childOccurrence_label]
  exact priorVertex_label_lt_parent G _ s

/-- The actual recursion inherits strict descent of the real predecessor labels. -/
theorem lssGarden_descendingLabels {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) :
    GardenTree.DescendingLabels (lssGarden G j) := by
  induction j using (measure (fun j : Fin n => j.val)).wf.induction with
  | h j ih =>
    rw [lssGarden_eq]
    refine ⟨?_, fun s => ih (priorVertex G j s) (priorVertex_lt G j s)⟩
    intro s
    rw [lssGarden_rootLabel]
    exact priorVertex_label_lt_parent G j s

theorem lssGarden_occurrenceLabel_le {n : ℕ} (G : SimpleGraph (Fin n))
    (j : Fin n) (o : GardenTree.Occurrence (lssGarden G j)) :
    GardenTree.occurrenceLabel (lssGarden G j) o ≤ j := by
  simpa only [lssGarden_rootLabel] using
    GardenTree.occurrenceLabel_le_root _ (lssGarden_descendingLabels G j) o

theorem lssGarden_occurrenceLabel_eq_iff_root {n : ℕ} (G : SimpleGraph (Fin n))
    (j : Fin n) (o : GardenTree.Occurrence (lssGarden G j)) :
    GardenTree.occurrenceLabel (lssGarden G j) o = j ↔
      GardenTree.IsRootOccurrence (lssGarden G j) o := by
  simpa only [lssGarden_rootLabel] using
    GardenTree.occurrenceLabel_eq_root_iff _ (lssGarden_descendingLabels G j) o

/-- Every occurrence in an immediate child's subtree is strictly below its parent. -/
theorem lssGarden_child_occurrenceLabel_lt {n : ℕ} (G : SimpleGraph (Fin n))
    (j : Fin n) (s : Fin (priorNonneighbors G j).length)
    (o : GardenTree.Occurrence (lssGarden G (priorVertex G j s))) :
    GardenTree.occurrenceLabel (lssGarden G (priorVertex G j s)) o < j :=
  lt_of_le_of_lt (lssGarden_occurrenceLabel_le G _ o) (priorVertex_label_lt_parent G j s)

/-- Earlier sibling slots have strictly earlier roots in the actual recursion trees. -/
theorem lssGarden_prior_sibling_rootLabel_lt {n : ℕ} (G : SimpleGraph (Fin n))
    (j : Fin n) (s t : Fin (priorNonneighbors G j).length) (hst : s < t) :
    (lssGarden G (priorVertex G j s)).rootLabel <
      (lssGarden G (priorVertex G j t)).rootLabel := by
  simp only [lssGarden_rootLabel]
  exact priorVertex_strictMono G j hst

/-- The ordered augmented sibling roots also have no same-class tie. -/
theorem lssGarden_augmented_sibling_rootLabel_lt {n : ℕ} (G : SimpleGraph (Fin n))
    (j i : Fin n) (s t : Fin (augmentedPriorNonneighbors G j i).length) (hst : s < t) :
    (lssGarden G (augmentedPriorVertex G j i s)).rootLabel <
      (lssGarden G (augmentedPriorVertex G j i t)).rootLabel := by
  simp only [lssGarden_rootLabel]
  exact augmentedPriorVertex_strictMono G j i hst

#assert_trust kernel GardenTree.occurrenceLabel_le_root
#assert_trust kernel GardenTree.occurrenceColors_childOccurrence
#assert_trust kernel GardenTree.occurrenceLabel_childOccurrence
#assert_trust kernel GardenTree.occurrenceLabel_eq_root_iff
#assert_trust kernel lssGarden_descendingLabels
#assert_trust kernel lssGarden_occurrenceLabel_eq_iff_root
#assert_trust kernel lssGarden_child_occurrenceLabel_lt
#assert_trust kernel lssGarden_childOccurrence_label
#assert_trust kernel lssGarden_childOccurrence_label_lt
#assert_trust kernel lssGarden_augmented_sibling_rootLabel_lt
#print axioms lssGarden_occurrenceLabel_eq_iff_root
#print axioms lssGarden_child_occurrenceLabel_lt
#print axioms lssGarden_childOccurrence_label_lt

end NLA.Proofs.SP11
