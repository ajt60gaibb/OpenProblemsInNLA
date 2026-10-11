import NLA.Proofs.MF03.FiniteTableauUniformSets

/-!
The tableau row condition gives equal-length suffix dominance for the
temporary uniform columns. Erasing the sentinel recovers precisely the
original one-gap noncollision inequality.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Taking a sorted uniform column's image preserves every suffix count. -/
theorem finiteTableauUniformLabels_suffix_image {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (p : Fin m) (q : ℕ) :
    finiteLabelSuffix (finiteTableauUniformLabels T p) q =
      finiteColumnSuffix (finiteTableauUniformValue T p) q := by
  unfold finiteLabelSuffix finiteTableauUniformLabels finiteColumnSuffix
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _
    (finiteTableauUniformValue_strictMono hj T p).injective]

/-- Uniform tableau columns obey the exact equal-length suffix dominance. -/
theorem finiteTableauUniformLabels_noncollision {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (p : Fin m) (hp : p.val + 1 < m) (q : ℕ) :
    finiteLabelSuffix (finiteTableauUniformLabels T p) q ≤
      finiteLabelSuffix
        (finiteTableauUniformLabels T ⟨p.val + 1, hp⟩) q := by
  let p' : Fin m := ⟨p.val + 1, hp⟩
  have hrow : ∀ r : Fin (m + 1),
      finiteTableauUniformValue T p r ≤
        finiteTableauUniformValue T p' r := by
    intro r
    exact finiteTableauUniformValue_row_monotone hj T r
      (show p ≤ p' from Fin.le_def.mpr (by simp [p']))
  have hcuts := (finiteColumnOrder_iff_suffix_same (m + 1)
    (finiteTableauUniformValue T p)
    (finiteTableauUniformValue T p')
    (finiteTableauUniformValue_strictMono hj T p)
    (finiteTableauUniformValue_strictMono hj T p')).mp hrow q
  rw [finiteTableauUniformLabels_suffix_image hj T p,
    finiteTableauUniformLabels_suffix_image hj T p']
  exact hcuts

/-- Erasing `N` removes exactly one suffix label in a short column at
every cut `q≤N`. -/
theorem finiteTableauUniformLabels_suffix_erase {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (p : Fin m) (q : ℕ) (hq : q ≤ N) :
    finiteLabelSuffix (finiteTableauUniformLabels T p) q =
      finiteLabelSuffix (finiteTableauActualLabels T p) q +
        (if p.val < j then 0 else 1) := by
  by_cases hp : p.val < j
  · have hnot : N ∉ finiteTableauUniformLabels T p := by
      intro hmem
      exact (finiteTableauUniformLabels_sentinel_iff hj T p).mp hmem hp
    have herase : finiteTableauActualLabels T p =
        finiteTableauUniformLabels T p := by
      simp [finiteTableauActualLabels, Finset.erase_eq_of_notMem hnot]
    simp [herase, hp]
  · have hmem : N ∈ finiteTableauUniformLabels T p :=
      (finiteTableauUniformLabels_sentinel_iff hj T p).mpr hp
    have hset : finiteTableauUniformLabels T p =
        insert N (finiteTableauActualLabels T p) := by
      simpa [finiteTableauActualLabels] using
        (Finset.insert_erase hmem).symm
    have hfresh : N ∉ (finiteTableauActualLabels T p).filter
        (fun k => q ≤ k) := by
      intro hN
      have hno : N ∉ finiteTableauActualLabels T p := by
        simp [finiteTableauActualLabels]
      exact hno (Finset.mem_filter.mp hN).1
    rw [hset]
    unfold finiteLabelSuffix
    rw [Finset.filter_insert, if_pos hq]
    simp [hp, Finset.card_insert_of_notMem hfresh]

/-- The tableau's actual labels satisfy the original, unsimplified
one-gap noncollision condition at every factor-label cut. -/
theorem finiteTableauActualLabels_noncollision {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N)
    (q : ℕ) (hq : q ≤ N)
    (p : Fin m) (hp : p.val + 1 < m) :
    finiteLabelSuffix (finiteTableauActualLabels T p) q ≤
      finiteLabelSuffix
        (finiteTableauActualLabels T ⟨p.val + 1, hp⟩) q +
          (if p.val + 1 = j then 1 else 0) := by
  let p' : Fin m := ⟨p.val + 1, hp⟩
  have hunif := finiteTableauUniformLabels_noncollision hj T p hp q
  change finiteLabelSuffix (finiteTableauUniformLabels T p) q ≤
    finiteLabelSuffix (finiteTableauUniformLabels T p') q at hunif
  rw [finiteTableauUniformLabels_suffix_erase hj T p q hq,
    finiteTableauUniformLabels_suffix_erase hj T p' q hq] at hunif
  change finiteLabelSuffix (finiteTableauActualLabels T p) q +
      (if p.val < j then 0 else 1) ≤
    finiteLabelSuffix (finiteTableauActualLabels T p') q +
      (if p'.val < j then 0 else 1) at hunif
  change finiteLabelSuffix (finiteTableauActualLabels T p) q ≤
    finiteLabelSuffix (finiteTableauActualLabels T p') q +
      (if p.val + 1 = j then 1 else 0)
  have hp' : p'.val = p.val + 1 := rfl
  by_cases hleft : p.val < j
  · by_cases hright : p'.val < j
    · have hgap : p.val + 1 ≠ j := by omega
      simp only [if_pos hleft, if_pos hright,
        if_neg hgap, Nat.add_zero] at hunif ⊢
      omega
    · have hgap : p.val + 1 = j := by omega
      simp only [if_pos hleft, if_neg hright,
        if_pos hgap, Nat.add_zero] at hunif ⊢
      omega
  · have hright : ¬ p'.val < j := by omega
    have hgap : p.val + 1 ≠ j := by omega
    simp only [if_neg hleft, if_neg hright,
      if_neg hgap, Nat.add_zero] at hunif ⊢
    omega

#assert_trust kernel finiteTableauActualLabels_noncollision
#print axioms finiteTableauActualLabels_noncollision

end NLA.Proofs.MF03
