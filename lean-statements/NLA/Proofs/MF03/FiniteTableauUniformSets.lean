import NLA.Proofs.MF03.FiniteTableauUniform

/-!
The uniform tableau columns as finite sets; erasing `N` recovers exactly
the actual advance-label sets, with their original long/short lengths.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- All values in a uniform tableau column. -/
noncomputable def finiteTableauUniformLabels {N m j : ℕ}
    (T : FiniteTableau (finiteAugShape m j) N) (p : Fin m) : Finset ℕ :=
  (Finset.univ : Finset (Fin (m + 1))).image
    (finiteTableauUniformValue T p)

/-- Each uniform tableau column has exactly `m+1` distinct values. -/
theorem finiteTableauUniformLabels_card {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (p : Fin m) :
    (finiteTableauUniformLabels T p).card = m + 1 := by
  unfold finiteTableauUniformLabels
  rw [Finset.card_image_of_injective _
    (finiteTableauUniformValue_strictMono hj T p).injective]
  simp

/-- Uniform tableau values are at most the temporary sentinel. -/
theorem finiteTableauUniformValue_le_N {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (p : Fin m) (r : Fin (m + 1)) :
    finiteTableauUniformValue T p r ≤ N := by
  by_cases hr : r.val < m
  · have hcell := finiteTableau_rect_cell m j r.val p.val hr p.isLt
    have hbound := T.2 r.val p.val hcell
    simpa [finiteTableauUniformValue, hr] using hbound.le
  · by_cases hp : p.val < j
    · have hcell := finiteTableau_bottom_cell m j hj p.val hp
      have hbound := T.2 m p.val hcell
      simpa [finiteTableauUniformValue, hr, hp] using hbound.le
    · simp [finiteTableauUniformValue, hr, hp]

/-- A long uniform tableau column has only actual values below `N`. -/
theorem finiteTableauUniformValue_lt_N_of_long {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (p : Fin m) (hp : p.val < j) (r : Fin (m + 1)) :
    finiteTableauUniformValue T p r < N := by
  by_cases hr : r.val < m
  · have hcell := finiteTableau_rect_cell m j r.val p.val hr p.isLt
    have hbound := T.2 r.val p.val hcell
    simpa [finiteTableauUniformValue, hr] using hbound
  · have hcell := finiteTableau_bottom_cell m j hj p.val hp
    have hbound := T.2 m p.val hcell
    simpa [finiteTableauUniformValue, hr, hp] using hbound

/-- The sentinel belongs to a uniform tableau label set exactly for a
short column. -/
theorem finiteTableauUniformLabels_sentinel_iff {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (p : Fin m) :
    N ∈ finiteTableauUniformLabels T p ↔ ¬ p.val < j := by
  constructor
  · intro hmem hp
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hmem
    have hlt := finiteTableauUniformValue_lt_N_of_long hj T p hp r
    omega
  · intro hp
    apply Finset.mem_image.mpr
    refine ⟨⟨m, by omega⟩, Finset.mem_univ _, ?_⟩
    simp [finiteTableauUniformValue, hp]

/-- Actual labels are the uniform set with its temporary sentinel erased. -/
noncomputable def finiteTableauActualLabels {N m j : ℕ}
    (T : FiniteTableau (finiteAugShape m j) N) (p : Fin m) : Finset ℕ :=
  (finiteTableauUniformLabels T p).erase N

/-- All actual labels are below the factor bound `N`. -/
theorem finiteTableauActualLabels_lt {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (p : Fin m) (k : ℕ) (hk : k ∈ finiteTableauActualLabels T p) :
    k < N := by
  have hmem : k ∈ finiteTableauUniformLabels T p :=
    (Finset.mem_erase.mp hk).2
  have hne : k ≠ N := (Finset.mem_erase.mp hk).1
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hmem
  have hle := finiteTableauUniformValue_le_N hj T p r
  omega

/-- The recovered actual labels have the exact original long/short
cardinalities; the sentinel is never counted. -/
theorem finiteTableauActualLabels_card {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (p : Fin m) :
    (finiteTableauActualLabels T p).card =
      if p.val < j then m + 1 else m := by
  by_cases hp : p.val < j
  · have hnot : N ∉ finiteTableauUniformLabels T p := by
      intro hmem
      exact (finiteTableauUniformLabels_sentinel_iff hj T p).mp hmem hp
    simp [finiteTableauActualLabels, hp,
      Finset.erase_eq_of_notMem hnot,
      finiteTableauUniformLabels_card hj T p]
  · have hmem : N ∈ finiteTableauUniformLabels T p :=
      (finiteTableauUniformLabels_sentinel_iff hj T p).mpr hp
    have hcard := Finset.card_erase_add_one hmem
    have hunif := finiteTableauUniformLabels_card hj T p
    simp only [finiteTableauActualLabels, if_neg hp]
    omega

#assert_trust kernel finiteTableauActualLabels_card
#print axioms finiteTableauActualLabels_card

end NLA.Proofs.MF03
