import NLA.Proofs.SP11.GardenColors
import NLA.Proofs.SP11.HistogramRigidity

/-!
# Vertex-class weights of the actual shared monomial exponents

The sum of a sorted subset's coordinates equals the sum of its original
conduit colors. Applying that weight only to one vertex class reads the total
incident-color sum from the actual shared-variable exponent histogram.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11

/-- A numeric weight of an actual increasing coordinate subset. -/
def coordinateSubsetWeight {d r : ℕ} (s : CoordinateSubset d r) : ℕ :=
  ∑ i, (s.val i).val

/-- Sorting permutes rather than changes the colors, including zero arity. -/
theorem sortedColors_weight_eq {d r : ℕ} (c : Fin r → Fin d)
    (hc : Function.Injective c) :
    coordinateSubsetWeight (sortedColors c hc) = ∑ i, (c i).val := by
  unfold coordinateSubsetWeight
  calc
    (∑ i, ((sortedColors c hc).val i).val) =
        ∑ i, ((sortedColors c hc).val (colorPermutation c hc i)).val :=
      (Equiv.sum_comp (colorPermutation c hc) _).symm
    _ = ∑ i, (c i).val := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg Fin.val (sortedColors_spec c hc i).symm

/-- Each vertex class has its own incident-color weight; other vertices
contribute exactly zero. Variables retain their original vertex labels. -/
noncomputable def vertexClassWeight {V : Type*} {d : ℕ} (arity : V → ℕ)
    (v : V) : ((u : V) × CoordinateSubset d (arity u)) → ℕ := by
  classical
  exact fun x => if x.1 = v then coordinateSubsetWeight x.2 else 0

/-- The actual single-node monomial exponent records exactly that node's
incident-color sum in its own vertex class, and zero in every other class. -/
theorem vertexClassWeight_colorExponent {V : Type*} [DecidableEq V] {d : ℕ} (arity : V → ℕ)
    (v u : V) (c : Fin (arity u) → Fin d) (hc : Function.Injective c) :
    Finsupp.linearCombination ℕ (vertexClassWeight (d := d) arity v)
      (colorExponent (fun s : CoordinateSubset d (arity u) => Sigma.mk u s) c) =
        if u = v then ∑ i, (c i).val else 0 := by
  classical
  simp only [colorExponent, dif_pos hc, Finsupp.linearCombination_single, one_smul,
    vertexClassWeight]
  rw [sortedColors_weight_eq c hc]

#assert_trust kernel sortedColors_weight_eq
#assert_trust kernel vertexClassWeight_colorExponent
#print axioms vertexClassWeight_colorExponent

end NLA.Proofs.SP11
