import NLA.Proofs.MF03.FiniteTableauCellSet

/-!
The exact product over the actual labels of one bounded MF-03 tableau
column uses its original cells, with no short-column sentinel.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.MF03

/-- Strict original tableau columns make the upper-cell value map injective. -/
private theorem finiteUpperCellLabels_injOn {N m j : ℕ}
    (T : FiniteTableau (finiteAugShape m j) N) (p : Fin m) :
    Set.InjOn (fun r : ℕ => T.1 r p.val) (Finset.range m : Set ℕ) := by
  intro r hr s hs heq
  have hrm : r < m := Finset.mem_range.mp hr
  have hsm : s < m := Finset.mem_range.mp hs
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcell := finiteTableau_rect_cell m j s p.val hsm p.isLt
    exact (ne_of_lt (T.1.col_strict hlt hcell)) heq
  · have hcell := finiteTableau_rect_cell m j r p.val hrm p.isLt
    exact (ne_of_gt (T.1.col_strict hgt hcell)) heq

/-- A product over upper original cell labels is their row product. -/
theorem finiteUpperCellLabels_product {N m j : ℕ}
    (T : FiniteTableau (finiteAugShape m j) N) (p : Fin m) :
    (∏ k ∈ finiteUpperCellLabels T p, cosineFactor (k + 1)) =
      ∏ r ∈ Finset.range m, cosineFactor (T.1 r p.val + 1) := by
  classical
  unfold finiteUpperCellLabels
  exact Finset.prod_image (finiteUpperCellLabels_injOn T p)

/-- The full actual-column product is exactly the product of original upper
cells, times the genuine bottom factor only in a long column. -/
theorem finiteTableauActualLabels_product {N m j : ℕ} (hj : j ≤ m)
    (T : FiniteTableau (finiteAugShape m j) N) (p : Fin m) :
    (∏ k ∈ finiteTableauActualLabels T p, cosineFactor (k + 1)) =
      (∏ r ∈ Finset.range m, cosineFactor (T.1 r p.val + 1)) *
        (if p.val < j then cosineFactor (T.1 m p.val + 1) else 1) := by
  classical
  rw [finiteTableauActualLabels_cells hj T p]
  by_cases hp : p.val < j
  · have hbot := finiteTableau_bottom_cell m j hj p.val hp
    have hdisj : Disjoint (finiteUpperCellLabels T p)
        ({T.1 m p.val} : Finset ℕ) := by
      apply Finset.disjoint_singleton_right.mpr
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨r, hr, heq⟩
      have hlt := T.1.col_strict (Finset.mem_range.mp hr) hbot
      exact (ne_of_lt hlt) heq
    simp only [if_pos hp]
    rw [Finset.prod_union hdisj, Finset.prod_singleton]
    exact congrArg (fun x : ℝ => x * cosineFactor (T.1 m p.val + 1))
      (finiteUpperCellLabels_product T p)
  · simp [hp, finiteUpperCellLabels_product]

#assert_trust kernel finiteUpperCellLabels_product
#assert_trust kernel finiteTableauActualLabels_product
#print axioms finiteTableauActualLabels_product

end NLA.Proofs.MF03
