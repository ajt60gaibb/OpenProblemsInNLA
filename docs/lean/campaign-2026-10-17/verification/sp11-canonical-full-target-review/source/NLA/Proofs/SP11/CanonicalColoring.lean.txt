import NLA.Proofs.SP11.LSSGarden
import NLA.Proofs.SP11.GardenColors
import NLA.Proofs.SP11.PriorListStructure

/-!
# Admissible canonical conduit colors

Ordinary children receive colors equal to their zero-based sibling positions.
A node's output color is at least its number of children. The structural child
arity bound guarantees that these choices give no repeated local color.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11.GardenTree

variable {V : Type*} {arity : V → ℕ} {d : ℕ}

/-- Number of input conduits at the root. -/
def rootArity : GardenTree V arity → ℕ
  | .node v _ => arity v

/-- Every node has enough available distinct colors for its local tensor. -/
def ArityBound (d : ℕ) : GardenTree V arity → Prop
  | .node v children => arity v < d ∧ ∀ s, ArityBound d (children s)

/-- The ordinary sibling-position inequality, imposed at every node. -/
def NormalStructure : GardenTree V arity → Prop
  | .node _ children =>
      (∀ s, rootArity (children s) ≤ s.val) ∧ ∀ s, NormalStructure (children s)

/-- No repeated color at any node's incident conduits. This is a property of a
single full coloring, not a claim about polynomial-variable independence. -/
def Admissible : (t : GardenTree V arity) → Coloring d t → Prop
  | .node _ children, c =>
      Function.Injective (Matrix.vecCons c.1 (fun s => rootColor (c.2 s))) ∧
      ∀ s, Admissible (children s) (c.2 s)

/-- Canonical ordinary tree coloring. Its top output color is supplied, while
every lower output is its zero-based position among its parent's children. -/
noncomputable def normalColoring : (t : GardenTree V arity) →
    ArityBound d t → Fin d → Coloring d t
  | .node _v children, h, q =>
      (q, fun s => normalColoring (children s) (h.2 s)
        ⟨s.val, lt_trans s.isLt h.1⟩)

@[simp] theorem rootColor_normalColoring (t : GardenTree V arity)
    (h : ArityBound d t) (q : Fin d) :
    rootColor (normalColoring t h q) = q := by
  cases t
  rfl

/-- Structural sibling bounds make the normal coloring genuinely admissible.
This is valid in every ambient dimension satisfying the explicit arity bound. -/
theorem normalColoring_admissible (t : GardenTree V arity)
    (h : ArityBound d t) (hs : NormalStructure t) (q : Fin d)
    (hq : rootArity t ≤ q.val) : Admissible t (normalColoring t h q) := by
  induction t generalizing q with
  | node v children ih =>
    change Function.Injective
      (Matrix.vecCons q (fun s => rootColor
        (normalColoring (children s) (h.2 s) ⟨s.val, lt_trans s.isLt h.1⟩))) ∧ _
    simp only [rootColor_normalColoring]
    constructor
    · apply Fin.cons_injective_of_injective
      · rintro ⟨s, hs⟩
        have hv : s.val = q.val := congrArg (fun z : Fin d => z.val) hs
        have hslt := s.isLt
        change arity v ≤ q.val at hq
        omega
      · intro i j hij
        exact Fin.ext (congrArg (fun z : Fin d => z.val) hij)
    · intro s
      exact ih s (h.2 s) (hs.2 s) ⟨s.val, lt_trans s.isLt h.1⟩ (hs.1 s)

/-- Root dimension follows from the all-node arity bound. -/
theorem rootArity_lt (t : GardenTree V arity) (h : ArityBound d t) :
    rootArity t < d := by
  cases t with
  | node v children => exact h.1

/-- Insert the output cap at any position among the root's ordinary children.
Below each child, the coloring is the normal coloring. -/
noncomputable def insertedColoring : (t : GardenTree V arity) →
    (h : ArityBound d t) → Fin (rootArity t + 1) → Coloring d t
  | .node _v children, h, p =>
      (Fin.castLE (Nat.succ_le_of_lt h.1) p,
        fun s => normalColoring (children s) (h.2 s)
          (Fin.castLE (Nat.succ_le_of_lt h.1) (p.succAbove s)))

/-- Skipping one cap slot never lowers a child's zero-based position. -/
theorem slot_le_succAbove {k : ℕ} (p : Fin (k + 1)) (s : Fin k) :
    s.val ≤ (p.succAbove s).val := by
  by_cases hs : s.castSucc < p
  · rw [Fin.succAbove_of_castSucc_lt p s hs]
    exact le_rfl
  · rw [Fin.succAbove_of_le_castSucc p s (le_of_not_gt hs)]
    exact Nat.le_succ _

/-- The special later-root coloring is admissible at every possible insertion
position; no favorable position or extra dimension is assumed. -/
theorem insertedColoring_admissible (t : GardenTree V arity)
    (h : ArityBound d t) (hs : NormalStructure t) (p : Fin (rootArity t + 1)) :
    Admissible t (insertedColoring t h p) := by
  cases t with
  | node v children =>
    change Function.Injective
      (Matrix.vecCons (Fin.castLE (Nat.succ_le_of_lt h.1) p)
        (fun s => rootColor (normalColoring (children s) (h.2 s)
          (Fin.castLE (Nat.succ_le_of_lt h.1) (p.succAbove s))))) ∧ _
    simp only [rootColor_normalColoring]
    constructor
    · apply Fin.cons_injective_of_injective
      · rintro ⟨s, he⟩
        exact p.succAbove_ne s ((Fin.castLE_injective _) he)
      · exact (Fin.castLE_injective _).comp Fin.succAbove_right_injective
    · intro s
      apply normalColoring_admissible (children s) (h.2 s) (hs.2 s)
      exact (hs.1 s).trans (slot_le_succAbove p s)

#assert_trust kernel normalColoring_admissible
#assert_trust kernel insertedColoring_admissible
#print axioms normalColoring_admissible
#print axioms insertedColoring_admissible

end NLA.Proofs.SP11.GardenTree

namespace NLA.Proofs.SP11

/-- The tree model retains the actual predecessor arity at its root. -/
theorem lssGarden_rootArity {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) :
    (lssGarden G j).rootArity = (priorNonneighbors G j).length := by
  rw [lssGarden_eq]
  rfl

/-- Every tree occurrence inherits the ambient arity bound of its original vertex. -/
theorem lssGarden_arityBound {n d : ℕ} (G : SimpleGraph (Fin n))
    (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d) (j : Fin n) :
    GardenTree.ArityBound d (lssGarden G j) := by
  induction j using (measure (fun j : Fin n => j.val)).wf.induction with
  | h j ih =>
    rw [lssGarden_eq]
    exact ⟨hd j, fun s => ih (priorVertex G j s) (priorVertex_lt G j s)⟩

/-- Hall's greedy sibling bound holds throughout each actual recursion tree. -/
theorem lssGarden_normalStructure {n : ℕ} (G : SimpleGraph (Fin n))
    (hgr : OrderedGreedy G) (j : Fin n) : GardenTree.NormalStructure (lssGarden G j) := by
  induction j using (measure (fun j : Fin n => j.val)).wf.induction with
  | h j ih =>
    rw [lssGarden_eq]
    refine ⟨?_, fun s => ih (priorVertex G j s) (priorVertex_lt G j s)⟩
    intro s
    rw [lssGarden_rootArity]
    exact hgr.priorVertex_arity_le_slot G j s

#assert_trust kernel lssGarden_arityBound
#assert_trust kernel lssGarden_normalStructure
#print axioms lssGarden_normalStructure

end NLA.Proofs.SP11
