import NLA.Proofs.SP11.DoubleRootGarden
import NLA.Proofs.SP11.ColorWeights

/-!
# Actual paired-garden histograms and incident-color sums

Nonzero paired signs imply distinct colors at every actual node occurrence.
The shared Sigma(vertex,subset) exponent then records exactly the sum of
incident colors in each original vertex class. This is a bridge from the
concrete signed polynomial expansion to the later uniqueness induction.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11.GardenTree

variable {V : Type*} {arity : V → ℕ} {d : ℕ}

/-- The original label of an actual node in the two-root occurrence set. -/
def doubleOccurrenceLabel (t u : GardenTree V arity) : DoubleOccurrence t u → V
  | .inl o => occurrenceLabel t o
  | .inr o => occurrenceLabel u o

/-- All colors incident to one actual node; both roots use the same cap color. -/
def doubleOccurrenceColors (t u : GardenTree V arity) (c : DoubleColoring d t u) :
    (o : DoubleOccurrence t u) →
      Fin (arity (doubleOccurrenceLabel t u o) + 1) → Fin d
  | .inl o => occurrenceColors t (leftColoring c) o
  | .inr o => occurrenceColors u (rightColoring c) o

/-- The sum of actual incident colors at one node, with zero-based color values. -/
def doubleIncidentSum (t u : GardenTree V arity) (c : DoubleColoring d t u)
    (o : DoubleOccurrence t u) : ℕ := ∑ s, (doubleOccurrenceColors t u c o s).val

/-- Read only the occurrences bearing the selected original vertex label. -/
noncomputable def classIncidentSum (t u : GardenTree V arity) (c : DoubleColoring d t u)
    (v : V) : ℕ := by
  classical
  exact ∑ o : DoubleOccurrence t u,
    if doubleOccurrenceLabel t u o = v then doubleIncidentSum t u c o else 0

/-- A nonzero paired coefficient excludes repeated colors at every actual node. -/
theorem doubleOccurrenceColors_injective_of_sign_ne_zero
    (t u : GardenTree V arity) (c : DoubleColoring d t u)
    (hsign : doubleColoringSign ℝ t u c ≠ 0) (o : DoubleOccurrence t u) :
    Function.Injective (doubleOccurrenceColors t u c o) := by
  classical
  have hf : ∀ o : DoubleOccurrence t u,
      (match o with
      | .inl o => colorSign ℝ (occurrenceColors t (leftColoring c) o)
      | .inr o => colorSign ℝ (occurrenceColors u (rightColoring c) o)) ≠ 0 := by
    exact fun o => Finset.prod_ne_zero_iff.mp hsign o (Finset.mem_univ o)
  have hn : colorSign ℝ (doubleOccurrenceColors t u c o) ≠ 0 := by
    cases o with
    | inl o => exact hf (.inl o)
    | inr o => exact hf (.inr o)
  by_contra hinj
  simp only [colorSign, dif_neg hinj] at hn
  exact hn rfl

/-- The linear weight of the actual occurrence exponent equals its class's
incident-color sum when every contributing local tuple is injective. -/
theorem vertexClassWeight_doubleColoringExponent_of_injective [DecidableEq V]
    (t u : GardenTree V arity) (c : DoubleColoring d t u) (v : V)
    (hinj : ∀ o, Function.Injective (doubleOccurrenceColors t u c o)) :
    Finsupp.linearCombination ℕ (vertexClassWeight (d := d) (fun v => arity v + 1) v)
      (doubleColoringExponent t u c) = classIncidentSum t u c v := by
  classical
  rw [doubleColoringExponent, map_sum]
  change (∑ o : DoubleOccurrence t u, _) = ∑ o : DoubleOccurrence t u, _
  apply Finset.sum_congr rfl
  intro o _
  cases o with
  | inl o =>
    convert vertexClassWeight_colorExponent (fun v => arity v + 1) v
      (occurrenceLabel t o) (occurrenceColors t (leftColoring c) o) (hinj (.inl o)) using 1
    · rfl
    · simp only [doubleOccurrenceLabel, doubleIncidentSum, doubleOccurrenceColors]
      split_ifs <;> simp_all <;> rfl
  | inr o =>
    convert vertexClassWeight_colorExponent (fun v => arity v + 1) v
      (occurrenceLabel u o) (occurrenceColors u (rightColoring c) o) (hinj (.inr o)) using 1
    · rfl
    · simp only [doubleOccurrenceLabel, doubleIncidentSum, doubleOccurrenceColors]
      split_ifs <;> simp_all <;> rfl


/-- Nonzero actual coefficients let the shared monomial histogram read each
vertex class's total incident-color sum, with multiplicities of occurrences. -/
theorem vertexClassWeight_doubleColoringExponent [DecidableEq V]
    (t u : GardenTree V arity) (c : DoubleColoring d t u) (v : V)
    (hsign : doubleColoringSign ℝ t u c ≠ 0) :
    Finsupp.linearCombination ℕ (vertexClassWeight (d := d) (fun v => arity v + 1) v)
      (doubleColoringExponent t u c) = classIncidentSum t u c v :=
  vertexClassWeight_doubleColoringExponent_of_injective t u c v
    (doubleOccurrenceColors_injective_of_sign_ne_zero t u c hsign)

/-- Equal shared-variable exponents force equal incident-color sums in every
original vertex class, even when the class has many repeated occurrences. -/
theorem classIncidentSum_eq_of_exponent_eq [DecidableEq V]
    (t u : GardenTree V arity) (actual best : DoubleColoring d t u)
    (ha : doubleColoringSign ℝ t u actual ≠ 0)
    (hb : doubleColoringSign ℝ t u best ≠ 0)
    (he : doubleColoringExponent t u actual = doubleColoringExponent t u best)
    (v : V) : classIncidentSum t u actual v = classIncidentSum t u best v := by
  have h := congrArg
    (Finsupp.linearCombination ℕ (vertexClassWeight (d := d) (fun v => arity v + 1) v)) he
  rwa [vertexClassWeight_doubleColoringExponent t u actual v ha,
    vertexClassWeight_doubleColoringExponent t u best v hb] at h

/-- If no occurrence in one class can improve its incident sum, equal actual
histograms force equality at every occurrence of that class. The one-sided
bounds remain explicit obligations of the greedy induction. -/
theorem doubleIncidentSum_eq_of_exponent_eq [DecidableEq V]
    (t u : GardenTree V arity) (actual best : DoubleColoring d t u)
    (ha : doubleColoringSign ℝ t u actual ≠ 0)
    (hb : doubleColoringSign ℝ t u best ≠ 0)
    (he : doubleColoringExponent t u actual = doubleColoringExponent t u best)
    (v : V)
    (hbound : ∀ o, doubleOccurrenceLabel t u o = v →
      doubleIncidentSum t u best o ≤ doubleIncidentSum t u actual o) :
    ∀ o, doubleOccurrenceLabel t u o = v →
      doubleIncidentSum t u actual o = doubleIncidentSum t u best o := by
  classical
  intro o ho
  by_contra hne
  have hstrict : doubleIncidentSum t u best o < doubleIncidentSum t u actual o :=
    lt_of_le_of_ne (hbound o ho) (Ne.symm hne)
  have hsum := classIncidentSum_eq_of_exponent_eq t u actual best ha hb he v
  have hlt : classIncidentSum t u best v < classIncidentSum t u actual v := by
    apply Finset.sum_lt_sum
    · intro q _
      by_cases hq : doubleOccurrenceLabel t u q = v
      · simpa only [if_pos hq] using hbound q hq
      · simp only [if_neg hq, le_refl]
    · exact ⟨o, Finset.mem_univ o, by simpa only [if_pos ho] using hstrict⟩
  rw [hsum] at hlt
  exact lt_irrefl _ hlt

#assert_trust kernel doubleOccurrenceColors_injective_of_sign_ne_zero
#assert_trust kernel vertexClassWeight_doubleColoringExponent
#assert_trust kernel classIncidentSum_eq_of_exponent_eq
#assert_trust kernel doubleIncidentSum_eq_of_exponent_eq
#print axioms vertexClassWeight_doubleColoringExponent
#print axioms doubleIncidentSum_eq_of_exponent_eq

end NLA.Proofs.SP11.GardenTree
