import NLA.Proofs.MF03.FiniteUniformColumnBounds
import NLA.Proofs.MF03.FiniteTableauTail

/-!
Fill only the cells of the original augmented Young diagram with sorted
uniform-column labels. The temporary bottom sentinel in a short column is
outside that diagram and contributes no tableau cell.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- The sorted uniform columns are monotone across arbitrary column gaps. -/
theorem finiteUniformColumn_row_monotone {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (r : Fin (m + 1)) :
    Monotone (fun p : Fin m => finiteUniformColumn D p r) := by
  cases m with
  | zero =>
      intro p _ _
      exact Fin.elim0 p
  | succ n =>
      apply Fin.monotone_iff_le_succ.mpr
      intro p
      exact finiteUniformColumn_row_weak D p.castSucc
        (by
          change p.val + 1 < n + 1
          omega) r

/-- Entry function, zero off the unchanged augmented diagram. -/
noncomputable def finiteColumnTableauEntry {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (r c : ℕ) : ℕ :=
  if hcell : (r, c) ∈ finiteAugShape m j then
    finiteUniformColumn D
      ⟨c, by
        rcases (mem_finiteAugShape m j r c).mp hcell with hrect | hbottom
        · exact hrect.2
        · exact lt_of_lt_of_le hbottom.2 (min_le_right j m)⟩
      ⟨r, by
        rcases (mem_finiteAugShape m j r c).mp hcell with hrect | hbottom
        · omega
        · omega⟩
  else 0

/-- At an original cell, the entry is the corresponding sorted label. -/
theorem finiteColumnTableauEntry_cell {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (r c : ℕ)
    (hcell : (r, c) ∈ finiteAugShape m j)
    (hc : c < m) (hr : r < m + 1) :
    finiteColumnTableauEntry D r c =
      finiteUniformColumn D ⟨c, hc⟩ ⟨r, hr⟩ := by
  simp only [finiteColumnTableauEntry, dif_pos hcell]

/-- A strict uniform column has strictly increasing entries. -/
theorem finiteUniformColumn_strictMono {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (p : Fin m) :
    StrictMono (finiteUniformColumn D p) :=
  finiteSortedColumn_strictMono _ _

/-- Every exact source-locked column system gives a bounded tableau of the
original augmented shape, with no sentinel in any cell. -/
noncomputable def finiteColumnSystemToTableau {N m j : ℕ}
    (D : FiniteColumnSystem N m j) (hj : j ≤ m) :
    FiniteTableau (finiteAugShape m j) N := by
  classical
  refine ⟨{
    entry := finiteColumnTableauEntry D
    row_weak' := ?_
    col_strict' := ?_
    zeros' := ?_
  }, ?_⟩
  · intro r c₁ c₂ hlt hcell₂
    have hcell₁ : (r, c₁) ∈ finiteAugShape m j :=
      (finiteAugShape m j).up_left_mem le_rfl (Nat.le_of_lt hlt) hcell₂
    have hpos₂ := (mem_finiteAugShape m j r c₂).mp hcell₂
    have hpos₁ := (mem_finiteAugShape m j r c₁).mp hcell₁
    have hc₁ : c₁ < m := by rcases hpos₁ with h | h <;> omega
    have hc₂ : c₂ < m := by rcases hpos₂ with h | h <;> omega
    have hr : r < m + 1 := by rcases hpos₂ with h | h <;> omega
    rw [finiteColumnTableauEntry_cell D r c₁ hcell₁ hc₁ hr,
      finiteColumnTableauEntry_cell D r c₂ hcell₂ hc₂ hr]
    exact finiteUniformColumn_row_monotone D ⟨r, hr⟩
      (show (⟨c₁, hc₁⟩ : Fin m) ≤ ⟨c₂, hc₂⟩ from
        Fin.le_def.mpr (Nat.le_of_lt hlt))
  · intro r₁ r₂ c hlt hcell₂
    have hcell₁ : (r₁, c) ∈ finiteAugShape m j :=
      (finiteAugShape m j).up_left_mem (Nat.le_of_lt hlt) le_rfl hcell₂
    have hpos₂ := (mem_finiteAugShape m j r₂ c).mp hcell₂
    have hc : c < m := by rcases hpos₂ with h | h <;> omega
    have hr₂ : r₂ < m + 1 := by rcases hpos₂ with h | h <;> omega
    have hr₁ : r₁ < m + 1 := by omega
    rw [finiteColumnTableauEntry_cell D r₁ c hcell₁ hc hr₁,
      finiteColumnTableauEntry_cell D r₂ c hcell₂ hc hr₂]
    exact finiteUniformColumn_strictMono D ⟨c, hc⟩
      (show (⟨r₁, hr₁⟩ : Fin (m + 1)) < ⟨r₂, hr₂⟩ from
        Fin.lt_def.mpr hlt)
  · intro r c hnot
    simp [finiteColumnTableauEntry, hnot]
  · intro r c hcell
    have hpos := (mem_finiteAugShape m j r c).mp hcell
    have hc : c < m := by rcases hpos with h | h <;> omega
    have hr : r < m + 1 := by rcases hpos with h | h <;> omega
    change finiteColumnTableauEntry D r c < N
    rw [finiteColumnTableauEntry_cell D r c hcell hc hr]
    rcases hpos with hrect | hbottom
    · exact finiteUniformColumn_lt_N_of_upper D ⟨c, hc⟩
        ⟨r, hr⟩ hrect.1
    · exact finiteUniformColumn_lt_N_of_long D ⟨c, hc⟩
        (by
          change c < j
          exact lt_of_lt_of_le hbottom.2 (min_le_left j m)) ⟨r, hr⟩

#assert_trust kernel finiteColumnSystemToTableau
#print axioms finiteColumnSystemToTableau

end NLA.Proofs.MF03
