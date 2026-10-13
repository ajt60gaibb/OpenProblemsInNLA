import NLA.Proofs.MF03.FiniteColumnSystem

/-!
Adjoin the temporary sentinel `N` to each short augmented-tableau column.
Every column then has exactly `m+1` labels. The sentinel is only a device
for proving the row inequalities and is not a tableau cell or weight.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Equal-length augmented label sets; actual labels remain unchanged. -/
def finiteUniformLabels {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m) : Finset ℕ :=
  if p.val < j then D.labels p else insert N (D.labels p)

private theorem finiteColumnSystem_N_fresh {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m) :
    N ∉ D.labels p := by
  intro hN
  have hlt := D.label_lt p N hN
  omega

/-- Each augmented label set has the common length `m+1`. -/
theorem finiteUniformLabels_card {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m) :
    (finiteUniformLabels D p).card = m + 1 := by
  by_cases hp : p.val < j
  · simp [finiteUniformLabels, hp, D.card_eq p]
  · have hfresh := finiteColumnSystem_N_fresh D p
    simp [finiteUniformLabels, hp,
      Finset.card_insert_of_notMem hfresh, D.card_eq p]

/-- The sentinel occurs exactly in the short columns. -/
theorem finiteUniformLabels_sentinel_iff {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m) :
    N ∈ finiteUniformLabels D p ↔ ¬ p.val < j := by
  by_cases hp : p.val < j
  · simp [finiteUniformLabels, hp, finiteColumnSystem_N_fresh D p]
  · simp [finiteUniformLabels, hp]

/-- Every uniform label is at most the temporary sentinel. -/
theorem finiteUniformLabels_le_N {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m)
    (k : ℕ) (hk : k ∈ finiteUniformLabels D p) : k ≤ N := by
  by_cases hp : p.val < j
  · have hreal : k ∈ D.labels p := by
      simpa [finiteUniformLabels, hp] using hk
    exact (D.label_lt p k hreal).le
  · have hmem : k = N ∨ k ∈ D.labels p := by
      simpa [finiteUniformLabels, hp] using hk
    rcases hmem with rfl | hreal
    · exact le_rfl
    · exact (D.label_lt p k hreal).le

/-- At a cut `q≤N`, a short column gains exactly one suffix label. -/
theorem finiteUniformLabels_suffix {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m)
    (q : ℕ) (hq : q ≤ N) :
    finiteLabelSuffix (finiteUniformLabels D p) q =
      finiteLabelSuffix (D.labels p) q +
        (if p.val < j then 0 else 1) := by
  by_cases hp : p.val < j
  · simp [finiteUniformLabels, hp]
  · have hfresh :
        N ∉ (D.labels p).filter (fun k => q ≤ k) := by
      intro hN
      exact finiteColumnSystem_N_fresh D p (Finset.mem_filter.mp hN).1
    have hfilter :
        (insert N (D.labels p)).filter (fun k => q ≤ k) =
          insert N ((D.labels p).filter (fun k => q ≤ k)) := by
      rw [Finset.filter_insert, if_pos hq]
    simp [finiteLabelSuffix, finiteUniformLabels, hp,
      hfilter, Finset.card_insert_of_notMem hfresh]

/-- Above the sentinel, no uniform column has any remaining label. -/
theorem finiteUniformLabels_suffix_zero {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m)
    (q : ℕ) (hq : N < q) :
    finiteLabelSuffix (finiteUniformLabels D p) q = 0 := by
  unfold finiteLabelSuffix
  apply Finset.card_eq_zero.mpr
  ext k
  constructor
  · intro hk
    have hmem := (Finset.mem_filter.mp hk).1
    have hge := (Finset.mem_filter.mp hk).2
    have hle := finiteUniformLabels_le_N D p k hmem
    exact False.elim (by omega)
  · intro hk
    simp at hk

/-- The source-locked one-gap noncollision condition becomes ordinary
equal-length suffix dominance after sentinel augmentation. -/
theorem finiteUniformLabels_noncollision {N m j : ℕ}
    (D : FiniteColumnSystem N m j)
    (p : Fin m) (hp : p.val + 1 < m) (q : ℕ) :
    finiteLabelSuffix (finiteUniformLabels D p) q ≤
      finiteLabelSuffix (finiteUniformLabels D ⟨p.val + 1, hp⟩) q := by
  let p' : Fin m := ⟨p.val + 1, hp⟩
  by_cases hq : q ≤ N
  · have hraw := D.noncollision q hq p hp
    change finiteLabelSuffix (D.labels p) q ≤
      finiteLabelSuffix (D.labels p') q +
        (if p.val + 1 = j then 1 else 0) at hraw
    have hl := finiteUniformLabels_suffix D p q hq
    have hr := finiteUniformLabels_suffix D p' q hq
    change finiteLabelSuffix (finiteUniformLabels D p) q ≤
      finiteLabelSuffix (finiteUniformLabels D p') q
    rw [hl, hr]
    have hp' : p'.val = p.val + 1 := rfl
    by_cases hleft : p.val < j
    · by_cases hright : p'.val < j
      · have hgap : p.val + 1 ≠ j := by omega
        simp [hleft, hright, hgap] at hraw ⊢
        omega
      · have hgap : p.val + 1 = j := by omega
        simp [hleft, hright, hgap] at hraw ⊢
        omega
    · have hright : ¬ p'.val < j := by omega
      have hgap : p.val + 1 ≠ j := by omega
      simp [hleft, hright, hgap] at hraw ⊢
      omega
  · have hq' : N < q := by omega
    rw [finiteUniformLabels_suffix_zero D p q hq',
      finiteUniformLabels_suffix_zero D ⟨p.val + 1, hp⟩ q hq']

/-- Uniform strict columns obtained by sorting the augmented label sets. -/
noncomputable def finiteUniformColumn {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m) :
    Fin (m + 1) → ℕ :=
  finiteSortedColumn (finiteUniformLabels D p)
    (finiteUniformLabels_card D p)

/-- The uniform sorted columns are weakly increasing across every row. -/
theorem finiteUniformColumn_row_weak {N m j : ℕ}
    (D : FiniteColumnSystem N m j)
    (p : Fin m) (hp : p.val + 1 < m) (r : Fin (m + 1)) :
    finiteUniformColumn D p r ≤
      finiteUniformColumn D ⟨p.val + 1, hp⟩ r := by
  let p' : Fin m := ⟨p.val + 1, hp⟩
  have hl : StrictMono (finiteUniformColumn D p) :=
    finiteSortedColumn_strictMono _ _
  have hr : StrictMono (finiteUniformColumn D p') :=
    finiteSortedColumn_strictMono _ _
  have horder := (finiteColumnOrder_iff_suffix_same (m + 1)
    (finiteUniformColumn D p) (finiteUniformColumn D p') hl hr).mpr
    (by
      intro q
      change finiteColumnSuffix
          (finiteSortedColumn (finiteUniformLabels D p)
            (finiteUniformLabels_card D p)) q ≤
        finiteColumnSuffix
          (finiteSortedColumn (finiteUniformLabels D p')
            (finiteUniformLabels_card D p')) q
      rw [finiteSortedColumn_suffix, finiteSortedColumn_suffix]
      exact finiteUniformLabels_noncollision D p hp q)
  exact horder r

#assert_trust kernel finiteUniformLabels_noncollision
#assert_trust kernel finiteUniformColumn_row_weak
#print axioms finiteUniformColumn_row_weak

end NLA.Proofs.MF03
