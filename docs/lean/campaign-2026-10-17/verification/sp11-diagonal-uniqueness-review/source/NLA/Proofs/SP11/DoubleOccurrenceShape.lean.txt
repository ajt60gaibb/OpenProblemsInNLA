import NLA.Proofs.SP11.DoubleHistogramWeights
import NLA.Proofs.SP11.LSSLabelBounds
import NLA.Proofs.SP11.ColorRigidity
import NLA.Proofs.SP11.ColoringExt

/-!
# Actual paired occurrences supply the class-rigidity data

The child map and incident sums below come from the actual recursion trees.
Only the final local blocker/tie shape remains a premise of the paired
coloring recovery theorem; no class-sum or child-label oracle is introduced.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11.GardenTree

variable {V : Type*} {arity : V → ℕ} {d : ℕ}

/-- An actual child edge remains on its parent's side of the paired tree. -/
def doubleChildOccurrence (t u : GardenTree V arity) :
    (o : DoubleOccurrence t u) →
      Fin (arity (doubleOccurrenceLabel t u o)) → DoubleOccurrence t u
  | .inl o, s => .inl (childOccurrence t o s)
  | .inr o, s => .inr (childOccurrence u o s)

/-- Parent input and child output are the same actual conduit color. -/
theorem doubleOccurrenceColors_childOccurrence
    (t u : GardenTree V arity) (c : DoubleColoring d t u)
    (o : DoubleOccurrence t u) (s : Fin (arity (doubleOccurrenceLabel t u o))) :
    doubleOccurrenceColors t u c o s.succ =
      doubleOccurrenceColors t u c (doubleChildOccurrence t u o s) 0 := by
  cases o with
  | inl o => exact occurrenceColors_childOccurrence t (leftColoring c) o s
  | inr o => exact occurrenceColors_childOccurrence u (rightColoring c) o s

/-- The output value at one actual node occurrence. -/
def doubleOutputValue (t u : GardenTree V arity) (c : DoubleColoring d t u)
    (o : DoubleOccurrence t u) : ℕ := (doubleOccurrenceColors t u c o 0).val

/-- Split the exact incident tuple into its output and the outputs of its actual children. -/
theorem doubleIncidentSum_eq_output_add_children
    (t u : GardenTree V arity) (c : DoubleColoring d t u) (o : DoubleOccurrence t u) :
    doubleIncidentSum t u c o = doubleOutputValue t u c o +
      ∑ s : Fin (arity (doubleOccurrenceLabel t u o)),
        doubleOutputValue t u c (doubleChildOccurrence t u o s) := by
  rw [doubleIncidentSum, Fin.sum_univ_succ]
  apply congrArg (doubleOutputValue t u c o + ·)
  apply Finset.sum_congr rfl
  intro s _
  exact congrArg Fin.val (doubleOccurrenceColors_childOccurrence t u c o s)

/-- The conditional class sum is the literal sum over occurrences with that label. -/
theorem classIncidentSum_eq_filtered [DecidableEq V]
    (t u : GardenTree V arity) (c : DoubleColoring d t u) (v : V) :
    classIncidentSum t u c v =
      ∑ o ∈ Finset.univ.filter (fun o : DoubleOccurrence t u => doubleOccurrenceLabel t u o = v),
        doubleIncidentSum t u c o := by
  classical
  simp only [classIncidentSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : doubleOccurrenceLabel t u o = v
  · simp only [if_pos ho]
  · simp only [if_neg ho]

/-- Equal actual exponent histograms give exactly the class equation used by
color_eq_of_class_incident_sums_and_blockers, with actual child occurrences. -/
theorem classOutputIncidentSum_eq_of_exponent_eq [DecidableEq V]
    (t u : GardenTree V arity) (actual best : DoubleColoring d t u)
    (ha : doubleColoringSign ℝ t u actual ≠ 0)
    (hb : doubleColoringSign ℝ t u best ≠ 0)
    (he : doubleColoringExponent t u actual = doubleColoringExponent t u best) (v : V) :
    (∑ o ∈ Finset.univ.filter (fun o : DoubleOccurrence t u => doubleOccurrenceLabel t u o = v),
      (doubleOutputValue t u actual o +
        ∑ s : Fin (arity (doubleOccurrenceLabel t u o)),
          doubleOutputValue t u actual (doubleChildOccurrence t u o s))) =
    ∑ o ∈ Finset.univ.filter (fun o : DoubleOccurrence t u => doubleOccurrenceLabel t u o = v),
      (doubleOutputValue t u best o +
        ∑ s : Fin (arity (doubleOccurrenceLabel t u o)),
          doubleOutputValue t u best (doubleChildOccurrence t u o s)) := by
  have h := classIncidentSum_eq_of_exponent_eq t u actual best ha hb he v
  rw [classIncidentSum_eq_filtered, classIncidentSum_eq_filtered] at h
  simpa only [doubleIncidentSum_eq_output_add_children] using h

end GardenTree

/-- Actual paired LSS child labels are strictly earlier on either side. -/
theorem doubleLSS_childOccurrence_label_lt {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n)
    (o : GardenTree.DoubleOccurrence (lssGarden G i) (lssGarden G j))
    (s : Fin (priorNonneighbors G
      (GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j) o)).length) :
    GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j)
      (GardenTree.doubleChildOccurrence (lssGarden G i) (lssGarden G j) o s) <
    GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j) o := by
  cases o with
  | inl o => exact lssGarden_childOccurrence_label_lt G i o s
  | inr o => exact lssGarden_childOccurrence_label_lt G j o s

/-- Recover the actual paired summand index from its nonzero shared-variable
histogram once the local blocker/tie shape is supplied. All class sums, child
edges, and strict child-label facts are proved from the actual source data. -/
theorem doubleLSS_coloring_eq_of_exponent_eq_and_blockers {n d : ℕ}
    (G : SimpleGraph (Fin n)) (i j : Fin n)
    (actual best : GardenTree.DoubleColoring d (lssGarden G i) (lssGarden G j))
    (ha : GardenTree.doubleColoringSign ℝ (lssGarden G i) (lssGarden G j) actual ≠ 0)
    (hb : GardenTree.doubleColoringSign ℝ (lssGarden G i) (lssGarden G j) best ≠ 0)
    (he : GardenTree.doubleColoringExponent (lssGarden G i) (lssGarden G j) actual =
      GardenTree.doubleColoringExponent (lssGarden G i) (lssGarden G j) best)
    (hshape : ∀ o : GardenTree.DoubleOccurrence (lssGarden G i) (lssGarden G j),
      (∃ p,
        GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j) p <
          GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j) o ∧
        GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) actual o =
          GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) actual p ∧
        GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) best o =
          GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) best p) ∨
      (∀ q : ℕ, q < GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) best o →
        ∃ p,
          GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j) p <
            GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j) o ∧
          GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) best p = q ∧
          GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) actual o ≠
            GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) actual p)) :
    actual = best := by
  classical
  let t := lssGarden G i
  let u := lssGarden G j
  have hout := color_eq_of_class_incident_sums_and_blockers
    (GardenTree.doubleOccurrenceLabel t u)
    (fun o => Fin (priorNonneighbors G (GardenTree.doubleOccurrenceLabel t u o)).length)
    (GardenTree.doubleChildOccurrence t u)
    (doubleLSS_childOccurrence_label_lt G i j)
    (GardenTree.doubleOutputValue t u best) (GardenTree.doubleOutputValue t u actual)
    (GardenTree.classOutputIncidentSum_eq_of_exponent_eq t u actual best ha hb he) hshape
  apply GardenTree.doubleColoring_ext_of_occurrence_outputs t u actual best
  intro o
  exact Fin.ext (congrFun hout o)

#assert_trust kernel GardenTree.doubleOccurrenceColors_childOccurrence
#assert_trust kernel GardenTree.doubleIncidentSum_eq_output_add_children
#assert_trust kernel GardenTree.classOutputIncidentSum_eq_of_exponent_eq
#assert_trust kernel doubleLSS_childOccurrence_label_lt
#assert_trust kernel doubleLSS_coloring_eq_of_exponent_eq_and_blockers
#print axioms doubleLSS_coloring_eq_of_exponent_eq_and_blockers

end NLA.Proofs.SP11
