import NLA.Proofs.MF03.FiniteTableauUniformInverse

/-!
The source-locked augmented tableau is recovered cell for cell from its
actual labels. The sentinel remains outside the original shape.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Tableau → actual labels → sorted uniform columns → tableau is the
identity on the exact existing `FiniteTableau` type. -/
theorem finiteTableau_roundTrip {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N) :
    finiteColumnSystemToTableau (finiteTableauToColumnSystem hj T) hj = T := by
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro r c
  by_cases hcell : (r, c) ∈ finiteAugShape m j
  · have hpos := (mem_finiteAugShape m j r c).mp hcell
    have hc : c < m := by rcases hpos with h | h <;> omega
    have hr : r < m + 1 := by rcases hpos with h | h <;> omega
    change finiteColumnTableauEntry
      (finiteTableauToColumnSystem hj T) r c = T.1 r c
    rw [finiteColumnTableauEntry_cell
      (finiteTableauToColumnSystem hj T) r c hcell hc hr]
    rw [finiteTableauColumnSystem_sorted hj T ⟨c, hc⟩]
    rcases hpos with hrect | hbottom
    · simp [finiteTableauUniformValue, hrect.1]
    · have hp : c < j := lt_of_lt_of_le hbottom.2 (min_le_left j m)
      have hre : r = m := hbottom.1
      simp [finiteTableauUniformValue, hp, hre]
  · change finiteColumnTableauEntry
      (finiteTableauToColumnSystem hj T) r c = T.1 r c
    rw [T.1.zeros hcell]
    simp [finiteColumnTableauEntry, hcell]

#assert_trust kernel finiteTableau_roundTrip
#print axioms finiteTableau_roundTrip

end NLA.Proofs.MF03
