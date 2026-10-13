import NLA.Proofs.MF03.FiniteTableauColumnSystem

/-!
The sentinel-augmented labels recovered from a tableau are exactly its
uniform column images. Uniqueness of increasing finite-set enumeration
then recovers every tableau row value, including the temporary bottom.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Reaugmenting the tableau's actual labels exactly reproduces its
uniform image, with `N` inserted only in short columns. -/
theorem finiteTableauColumnSystem_uniformLabels {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (p : Fin m) :
    finiteUniformLabels (finiteTableauToColumnSystem hj T) p =
      finiteTableauUniformLabels T p := by
  change (if p.val < j then finiteTableauActualLabels T p
    else insert N (finiteTableauActualLabels T p)) =
      finiteTableauUniformLabels T p
  by_cases hp : p.val < j
  · have hnot : N ∉ finiteTableauUniformLabels T p := by
      intro hmem
      exact (finiteTableauUniformLabels_sentinel_iff hj T p).mp hmem hp
    simp [hp, finiteTableauActualLabels,
      Finset.erase_eq_of_notMem hnot]
  · have hmem : N ∈ finiteTableauUniformLabels T p :=
      (finiteTableauUniformLabels_sentinel_iff hj T p).mpr hp
    simpa [hp, finiteTableauActualLabels] using
      (Finset.insert_erase hmem)

/-- Sorting the recovered uniform set gives back every uniform tableau
value, by uniqueness of the strictly increasing enumeration. -/
theorem finiteTableauColumnSystem_sorted {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (p : Fin m) :
    finiteUniformColumn (finiteTableauToColumnSystem hj T) p =
      finiteTableauUniformValue T p := by
  let D : FiniteColumnSystem N m j := finiteTableauToColumnSystem hj T
  have hmem : ∀ r : Fin (m + 1),
      finiteTableauUniformValue T p r ∈ finiteUniformLabels D p := by
    intro r
    rw [show finiteUniformLabels D p = finiteTableauUniformLabels T p from
      finiteTableauColumnSystem_uniformLabels hj T p]
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  have hunique := Finset.orderEmbOfFin_unique
    (finiteUniformLabels_card D p) hmem
    (finiteTableauUniformValue_strictMono hj T p)
  change finiteTableauUniformValue T p = finiteUniformColumn D p at hunique
  exact hunique.symm

#assert_trust kernel finiteTableauColumnSystem_uniformLabels
#assert_trust kernel finiteTableauColumnSystem_sorted
#print axioms finiteTableauColumnSystem_sorted

end NLA.Proofs.MF03
