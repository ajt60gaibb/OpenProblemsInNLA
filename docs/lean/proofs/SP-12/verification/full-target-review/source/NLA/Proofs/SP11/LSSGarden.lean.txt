import NLA.Proofs.SP11.GardenTree

/-!
# The finite tree of the actual polynomial LSS recursion

Every child is the actual earlier nonneighbor. Repeated copies of an earlier
vertex retain that vertex label and its original coefficient family.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11

/-- Actual recursive LSS trees, with one child per earlier nonneighbor. -/
noncomputable def lssGarden {n : ℕ} (G : SimpleGraph (Fin n)) :
    Fin n → GardenTree (Fin n) (fun j => (priorNonneighbors G j).length) :=
  (measure (fun j : Fin n => j.val)).wf.fix
    (fun j rec => GardenTree.node j
      (fun s => rec (priorVertex G j s) (priorVertex_lt G j s)))

theorem lssGarden_eq {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) :
    lssGarden G j = GardenTree.node j (fun s => lssGarden G (priorVertex G j s)) := by
  unfold lssGarden
  rw [WellFounded.fix_eq]

/-- Tree evaluation is exactly uniformLSS, rather than an independent tree model. -/
theorem lssGarden_value {R : Type*} [CommRing R] {n d : ℕ}
    (G : SimpleGraph (Fin n)) (a : VertexForms G R d) (j : Fin n) :
    GardenTree.value a (lssGarden G j) = uniformLSS G a j := by
  induction j using (measure (fun j : Fin n => j.val)).wf.induction with
  | h j ih =>
    rw [lssGarden_eq]
    change alternatingContraction (a j)
      (fun s => GardenTree.value a (lssGarden G (priorVertex G j s))) = _
    rw [uniformLSS_eq]
    apply congrArg (alternatingContraction (a j))
    funext s
    exact ih (priorVertex G j s) (priorVertex_lt G j s)

/-- Exact conduit-color expansion of every row of the concrete polynomial LSS
matrix, over the same shared-variable polynomial ring as the original recursion. -/
theorem polynomialLSS_eq_sum_garden {n d : ℕ}
    (G : SimpleGraph (Fin n)) (j : Fin n) :
    polynomialLSS G d j =
      ∑ c : GardenTree.Coloring d (lssGarden G j),
        GardenTree.weight (universalVertexForms G) (lssGarden G j) c •
          Pi.single (GardenTree.rootColor c) 1 := by
  change uniformLSS G (universalVertexForms G) j = _
  rw [← lssGarden_value G (universalVertexForms G) j]
  exact GardenTree.value_eq_sum_weight _ _

#assert_trust kernel lssGarden_eq
#assert_trust kernel lssGarden_value
#assert_trust kernel polynomialLSS_eq_sum_garden
#print axioms polynomialLSS_eq_sum_garden

end NLA.Proofs.SP11
