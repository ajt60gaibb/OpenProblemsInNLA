import NLA.Proofs.MF03.FiniteTableauRoundTrip

/-!
The tableau made from an exact column system reads back the same uniform
sorted values and the same actual, sentinel-free label sets.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- The forward tableau's uniform value at every row is the original
sorted uniform label, including `N` at omitted short bottoms. -/
theorem finiteColumnSystem_tableau_uniformValue {N m j : ℕ}
    (hj : j ≤ m) (D : FiniteColumnSystem N m j)
    (p : Fin m) (r : Fin (m + 1)) :
    finiteTableauUniformValue (finiteColumnSystemToTableau D hj) p r =
      finiteUniformColumn D p r := by
  by_cases hr : r.val < m
  · have hcell := finiteTableau_rect_cell m j r.val p.val hr p.isLt
    change (if r.val < m then finiteColumnTableauEntry D r.val p.val
      else if p.val < j then finiteColumnTableauEntry D m p.val else N) = _
    rw [if_pos hr]
    exact finiteColumnTableauEntry_cell D r.val p.val hcell p.isLt r.isLt
  · have hreq : r.val = m := by have := r.isLt; omega
    by_cases hp : p.val < j
    · have hcell := finiteTableau_bottom_cell m j hj p.val hp
      change (if r.val < m then finiteColumnTableauEntry D r.val p.val
        else if p.val < j then finiteColumnTableauEntry D m p.val else N) = _
      rw [if_neg hr, if_pos hp]
      have hlast : r = ⟨m, by omega⟩ := Fin.ext hreq
      rw [hlast]
      exact finiteColumnTableauEntry_cell D m p.val hcell p.isLt (by omega)
    · change (if r.val < m then finiteColumnTableauEntry D r.val p.val
        else if p.val < j then finiteColumnTableauEntry D m p.val else N) = _
      rw [if_neg hr, if_neg hp]
      have hlast : r = ⟨m, by omega⟩ := Fin.ext hreq
      rw [hlast]
      exact (finiteUniformColumn_last D p (by omega)).symm

/-- The recovered uniform image of the forward tableau is exactly the
original sentinel-augmented set. -/
theorem finiteColumnSystem_tableau_uniformLabels {N m j : ℕ}
    (hj : j ≤ m) (D : FiniteColumnSystem N m j)
    (p : Fin m) :
    finiteTableauUniformLabels (finiteColumnSystemToTableau D hj) p =
      finiteUniformLabels D p := by
  change (Finset.univ : Finset (Fin (m + 1))).image
      (finiteTableauUniformValue (finiteColumnSystemToTableau D hj) p) = _
  have hfun : finiteTableauUniformValue
      (finiteColumnSystemToTableau D hj) p = finiteUniformColumn D p :=
    funext (finiteColumnSystem_tableau_uniformValue hj D p)
  rw [hfun]
  exact finiteSortedColumn_image _ _

/-- Erasing the temporary sentinel from the forward tableau recovers
every original actual label set. -/
theorem finiteColumnSystem_tableau_actualLabels {N m j : ℕ}
    (hj : j ≤ m) (D : FiniteColumnSystem N m j)
    (p : Fin m) :
    finiteTableauActualLabels (finiteColumnSystemToTableau D hj) p =
      D.labels p := by
  change (finiteTableauUniformLabels
    (finiteColumnSystemToTableau D hj) p).erase N = D.labels p
  rw [finiteColumnSystem_tableau_uniformLabels hj D p]
  have hfresh : N ∉ D.labels p := by
    intro hN
    have := D.label_lt p N hN
    omega
  by_cases hp : p.val < j
  · simp [finiteUniformLabels, hp, Finset.erase_eq_of_notMem hfresh]
  · simp [finiteUniformLabels, hp, Finset.erase_insert hfresh]

/-- Two exact column systems are equal when their actual labels agree. -/
theorem finiteColumnSystem_ext {N m j : ℕ}
    (D E : FiniteColumnSystem N m j)
    (h : ∀ p : Fin m, D.labels p = E.labels p) : D = E := by
  cases D with
  | mk labels hlt hcard hnc =>
    cases E with
    | mk labels' hlt' hcard' hnc' =>
      have heq : labels = labels' := by
        funext p
        exact h p
      subst labels'
      rfl

/-- Column system → exact tableau → actual label system is the identity. -/
theorem finiteColumnSystem_roundTrip {N m j : ℕ}
    (hj : j ≤ m) (D : FiniteColumnSystem N m j) :
    finiteTableauToColumnSystem hj (finiteColumnSystemToTableau D hj) = D := by
  apply finiteColumnSystem_ext
  intro p
  exact finiteColumnSystem_tableau_actualLabels hj D p

#assert_trust kernel finiteColumnSystem_tableau_uniformValue
#assert_trust kernel finiteColumnSystem_tableau_actualLabels
#assert_trust kernel finiteColumnSystem_roundTrip
#print axioms finiteColumnSystem_tableau_actualLabels

end NLA.Proofs.MF03
