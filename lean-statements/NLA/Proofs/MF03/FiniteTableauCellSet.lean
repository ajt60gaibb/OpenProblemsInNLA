import NLA.Proofs.MF03.FiniteTableauColumnEquiv

/-!
The actual labels of one bounded MF-03 augmented-tableau column are
exactly its original cells. Products use only those cells and never the
temporary short-column sentinel.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.MF03

/-- Values of the original upper `m` cells in one tableau column. -/
noncomputable def finiteUpperCellLabels {N m j : ℕ}
    (T : FiniteTableau (finiteAugShape m j) N) (p : Fin m) : Finset ℕ :=
  (Finset.range m).image (fun r => T.1 r p.val)

/-- Erasing the temporary sentinel leaves exactly the original upper
cells and, in a long column, its genuine bottom cell. -/
theorem finiteTableauActualLabels_cells {N m j : ℕ} (hj : j ≤ m)
    (T : FiniteTableau (finiteAugShape m j) N) (p : Fin m) :
    finiteTableauActualLabels T p =
      finiteUpperCellLabels T p ∪
        (if p.val < j then {T.1 m p.val} else ∅) := by
  classical
  ext k
  simp only [finiteTableauActualLabels, Finset.mem_erase,
    finiteTableauUniformLabels, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_union, finiteUpperCellLabels]
  constructor
  · rintro ⟨hkN, ⟨r, hr⟩⟩
    by_cases hupper : r.val < m
    · left
      exact ⟨r.val, Finset.mem_range.mpr hupper,
        by simpa [finiteTableauUniformValue, hupper] using hr⟩
    · have hlast : r.val = m := by have := r.isLt; omega
      have hp : p.val < j := by
        by_contra hp
        have hval : finiteTableauUniformValue T p r = N := by
          simp [finiteTableauUniformValue, hupper, hp]
        exact hkN (hr ▸ hval)
      right
      simp only [if_pos hp, Finset.mem_singleton]
      simpa [finiteTableauUniformValue, hupper, hp] using hr.symm
  · intro hk
    rcases hk with ⟨r, hr, hval⟩ | hbottom
    · have hrm : r < m := Finset.mem_range.mp hr
      have hcell := finiteTableau_rect_cell m j r p.val hrm p.isLt
      have hlt := T.2 r p.val hcell
      constructor
      · intro heq
        omega
      · exact ⟨⟨r, by omega⟩, by
          simpa [finiteTableauUniformValue, hrm] using hval⟩
    · by_cases hp : p.val < j
      · have hval : k = T.1 m p.val := by
          simpa [hp] using hbottom
        have hcell := finiteTableau_bottom_cell m j hj p.val hp
        have hlt := T.2 m p.val hcell
        constructor
        · intro heq
          omega
        · exact ⟨⟨m, by omega⟩, by
            simpa [finiteTableauUniformValue, hp] using hval.symm⟩
      · simp [hp] at hbottom

#assert_trust kernel finiteTableauActualLabels_cells
#print axioms finiteTableauActualLabels_cells

end NLA.Proofs.MF03
