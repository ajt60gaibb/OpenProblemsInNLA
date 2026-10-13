import NLA.Proofs.MF03.FiniteUniformColumns

/-!
Identify the temporary sentinel in each short sorted column. Only cells
of the original augmented diagram are subsequently given tableau entries.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Every sorted uniform-column entry is one of its augmented labels. -/
theorem finiteUniformColumn_mem {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m) (r : Fin (m + 1)) :
    finiteUniformColumn D p r ∈ finiteUniformLabels D p :=
  finiteSortedColumn_mem _ _ r

/-- Uniform-column entries never exceed the temporary sentinel. -/
theorem finiteUniformColumn_le_N {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m) (r : Fin (m + 1)) :
    finiteUniformColumn D p r ≤ N :=
  finiteUniformLabels_le_N D p _ (finiteUniformColumn_mem D p r)

/-- In each short column, the added sentinel is exactly the last entry. -/
theorem finiteUniformColumn_last {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m) (hp : j ≤ p.val) :
    finiteUniformColumn D p ⟨m, by omega⟩ = N := by
  have hsent : N ∈ finiteUniformLabels D p :=
    (finiteUniformLabels_sentinel_iff D p).mpr (by omega)
  have himage : N ∈ (Finset.univ : Finset (Fin (m + 1))).image
      (finiteUniformColumn D p) := by
    change N ∈ (Finset.univ : Finset (Fin (m + 1))).image
      (finiteSortedColumn (finiteUniformLabels D p)
        (finiteUniformLabels_card D p))
    rw [finiteSortedColumn_image]
    exact hsent
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp himage
  have hr_last : r = ⟨m, by omega⟩ := by
    apply Fin.ext
    change r.val = m
    by_contra hne
    have hlt : r < (⟨m, by omega⟩ : Fin (m + 1)) :=
      Fin.lt_def.mpr (by
        change r.val < m
        have := r.isLt
        omega)
    have hstrict := (finiteSortedColumn_strictMono
      (finiteUniformLabels D p) (finiteUniformLabels_card D p)) hlt
    have hle := finiteUniformColumn_le_N D p ⟨m, by omega⟩
    change finiteUniformColumn D p r <
      finiteUniformColumn D p ⟨m, by omega⟩ at hstrict
    omega
  simpa [hr_last] using hr

/-- An entry in a long column is an actual advance label, hence `<N`. -/
theorem finiteUniformColumn_lt_N_of_long {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m) (hp : p.val < j)
    (r : Fin (m + 1)) :
    finiteUniformColumn D p r < N := by
  have hmem := finiteUniformColumn_mem D p r
  have hreal : finiteUniformColumn D p r ∈ D.labels p := by
    simpa [finiteUniformLabels, hp] using hmem
  exact D.label_lt p _ hreal

/-- Every nonbottom sorted entry in a short column is an actual label. -/
theorem finiteUniformColumn_lt_N_of_upper {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m)
    (r : Fin (m + 1)) (hr : r.val < m) :
    finiteUniformColumn D p r < N := by
  by_cases hp : p.val < j
  · exact finiteUniformColumn_lt_N_of_long D p hp r
  · have hstrict := (finiteSortedColumn_strictMono
        (finiteUniformLabels D p) (finiteUniformLabels_card D p))
        (show r < (⟨m, by omega⟩ : Fin (m + 1)) from Fin.lt_def.mpr hr)
    change finiteUniformColumn D p r <
      finiteUniformColumn D p ⟨m, by omega⟩ at hstrict
    rw [finiteUniformColumn_last D p (by omega)] at hstrict
    exact hstrict

#assert_trust kernel finiteUniformColumn_last
#assert_trust kernel finiteUniformColumn_lt_N_of_upper
#print axioms finiteUniformColumn_lt_N_of_upper

end NLA.Proofs.MF03
