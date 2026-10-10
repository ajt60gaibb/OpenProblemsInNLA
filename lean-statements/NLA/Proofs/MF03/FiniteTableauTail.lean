import Mathlib
import LeanCert.Tactic.Verification
import NLA.Proofs.MF03.CosineCoefficientTransfer

/-! Finite-tableau restriction and a bottom-row entry bound for the MF-03 Schur gate.
This module does not identify tableau sums with Toeplitz determinants or prove
the weighted tail inequality. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.MF03

private def rectCells (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range m).product (Finset.range m)

private def bottomCells (m j : ℕ) : Finset (ℕ × ℕ) :=
  ({m} : Finset ℕ).product (Finset.range (min j m))

/-- The `m` by `m` rectangular Young diagram. -/
def finiteRectShape (m : ℕ) : YoungDiagram where
  cells := rectCells m
  isLowerSet := by
    rintro ⟨R, C⟩ ⟨r, c⟩ ⟨hr, hc⟩ hmem
    change (r, c) ∈ rectCells m
    change (R, C) ∈ rectCells m at hmem
    have hpair : R < m ∧ C < m := by
      simpa [rectCells] using (Finset.mem_product.mp hmem)
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr (hr.trans_lt hpair.1),
      Finset.mem_range.mpr (hc.trans_lt hpair.2)⟩

/-- A rectangular Young diagram with a bottom row of length `min j m`. -/
def finiteAugShape (m j : ℕ) : YoungDiagram where
  cells := rectCells m ∪ bottomCells m j
  isLowerSet := by
    rintro ⟨R, C⟩ ⟨r, c⟩ ⟨hr, hc⟩ hmem
    change (r, c) ∈ rectCells m ∪ bottomCells m j
    change (R, C) ∈ rectCells m ∪ bottomCells m j at hmem
    rw [Finset.mem_union] at hmem ⊢
    rcases hmem with hrect | hbottom
    · have hpair : R < m ∧ C < m := by
        simpa [rectCells] using (Finset.mem_product.mp hrect)
      exact Or.inl (Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (hr.trans_lt hpair.1),
          Finset.mem_range.mpr (hc.trans_lt hpair.2)⟩)
    · have hpair : R = m ∧ C < min j m := by
        rcases Finset.mem_product.mp hbottom with ⟨hR, hC⟩
        exact ⟨Finset.mem_singleton.mp hR, Finset.mem_range.mp hC⟩
      by_cases hlt : r < m
      · exact Or.inl (Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr hlt,
            Finset.mem_range.mpr
              (lt_of_le_of_lt hc (hpair.2.trans_le (min_le_right _ _)))⟩)
      · have hre : r = m := by omega
        exact Or.inr (Finset.mem_product.mpr
          ⟨Finset.mem_singleton.mpr hre,
            Finset.mem_range.mpr (hc.trans_lt hpair.2)⟩)

@[simp] theorem mem_finiteRectShape (m r c : ℕ) :
    (r, c) ∈ finiteRectShape m ↔ r < m ∧ c < m := by
  simp [finiteRectShape, rectCells]

@[simp] theorem mem_finiteAugShape (m j r c : ℕ) :
    (r, c) ∈ finiteAugShape m j ↔
      (r < m ∧ c < m) ∨ (r = m ∧ c < min j m) := by
  change (r, c) ∈ rectCells m ∪ bottomCells m j ↔ _
  rw [Finset.mem_union]
  constructor
  · intro h
    rcases h with hrect | hbottom
    · have hp := Finset.mem_product.mp hrect
      exact Or.inl ⟨Finset.mem_range.mp hp.1, Finset.mem_range.mp hp.2⟩
    · have hp := Finset.mem_product.mp hbottom
      exact Or.inr ⟨Finset.mem_singleton.mp hp.1,
        Finset.mem_range.mp hp.2⟩
  · intro h
    rcases h with ⟨hr, hc⟩ | ⟨hr, hc⟩
    · exact Or.inl (Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hr, Finset.mem_range.mpr hc⟩)
    · exact Or.inr (Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr hr,
          Finset.mem_range.mpr hc⟩)

/-- A semistandard tableau whose entries on its finite diagram are `< N`. -/
def FiniteTableau (μ : YoungDiagram) (N : ℕ) : Type :=
  {T : SemistandardYoungTableau μ //
    ∀ r c : ℕ, (r, c) ∈ μ → T r c < N}

private instance finiteTableau_finite (μ : YoungDiagram) (N : ℕ) :
    Finite (FiniteTableau μ N) := by
  let f : FiniteTableau μ N → (μ.cells → Fin N) :=
    fun T p => ⟨T.1 p.1.1 p.1.2,
      T.2 p.1.1 p.1.2 (by exact p.2)⟩
  apply Finite.of_injective f
  intro T U heq
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro r c
  by_cases hcell : (r, c) ∈ μ
  · have h := congrFun heq ⟨(r, c), by simpa using hcell⟩
    exact congrArg Fin.val h
  · rw [T.1.zeros hcell, U.1.zeros hcell]

noncomputable instance finiteTableau_fintype (μ : YoungDiagram) (N : ℕ) :
    Fintype (FiniteTableau μ N) := Fintype.ofFinite _

noncomputable def finiteRectWeight (m : ℕ) (T : ℕ → ℕ → ℕ) : ℝ :=
  ∏ r ∈ Finset.range m, ∏ c ∈ Finset.range m,
    cosineFactor (T r c + 1)

noncomputable def finiteBottomWeight (j m : ℕ) (T : ℕ → ℕ → ℕ) : ℝ :=
  ∏ c ∈ Finset.range j, cosineFactor (T m c + 1)

/-- Weighted finite rectangular tableau sum; no determinant claim is made. -/
noncomputable def finiteRectTableauSum (N m : ℕ) : ℝ :=
  ∑ T : FiniteTableau (finiteRectShape m) N, finiteRectWeight m T.1

/-- Weighted finite augmented-tableau sum; no determinant claim is made. -/
noncomputable def finiteAugTableauSum (N m j : ℕ) : ℝ :=
  ∑ T : FiniteTableau (finiteAugShape m j) N,
    finiteRectWeight m T.1 * finiteBottomWeight j m T.1

private theorem tableau_entry_ge_row {μ : YoungDiagram}
    (T : SemistandardYoungTableau μ) {r c : ℕ}
    (hcell : (r, c) ∈ μ) : r ≤ T r c := by
  induction r with
  | zero => exact Nat.zero_le _
  | succ r ih =>
      have hprev : (r, c) ∈ μ :=
        μ.up_left_mem (by omega : r ≤ r + 1) le_rfl hcell
      have hstrict : T r c < T (r + 1) c :=
        T.col_strict (Nat.lt_succ_self r) hcell
      have hbefore := ih hprev
      omega

private theorem rect_mem_aug (m j r c : ℕ)
    (h : (r, c) ∈ finiteRectShape m) :
    (r, c) ∈ finiteAugShape m j := by
  have hp := (mem_finiteRectShape m r c).mp h
  exact (mem_finiteAugShape m j r c).mpr (Or.inl hp)

private def restrictRectTableau (m j : ℕ)
    (T : SemistandardYoungTableau (finiteAugShape m j)) :
    SemistandardYoungTableau (finiteRectShape m) where
  entry r c := if (r, c) ∈ finiteRectShape m then T r c else 0
  row_weak' := by
    intro r c₁ c₂ hlt hcell
    have hcell₁ : (r, c₁) ∈ finiteRectShape m :=
      (finiteRectShape m).up_left_mem le_rfl (Nat.le_of_lt hlt) hcell
    simp only [if_pos hcell, if_pos hcell₁]
    exact T.row_weak hlt (rect_mem_aug m j r c₂ hcell)
  col_strict' := by
    intro r₁ r₂ c hlt hcell
    have hcell₁ : (r₁, c) ∈ finiteRectShape m :=
      (finiteRectShape m).up_left_mem (Nat.le_of_lt hlt) le_rfl hcell
    simp only [if_pos hcell, if_pos hcell₁]
    exact T.col_strict hlt (rect_mem_aug m j r₂ c hcell)
  zeros' := by
    intro r c hnot
    simp [hnot]

def finiteRectRestrict (N m j : ℕ)
    (T : FiniteTableau (finiteAugShape m j) N) :
    FiniteTableau (finiteRectShape m) N := by
  refine ⟨restrictRectTableau m j T.1, ?_⟩
  intro r c hcell
  have hbound := T.2 r c (rect_mem_aug m j r c hcell)
  change (if (r, c) ∈ finiteRectShape m then T.1 r c else 0) < N
  rw [if_pos hcell]
  exact hbound

private theorem bottom_cell_mem (m j c : ℕ) (hj : j ≤ m) (hc : c < j) :
    (m, c) ∈ finiteAugShape m j := by
  apply (mem_finiteAugShape m j m c).mpr
  right
  exact ⟨rfl, by simpa [min_eq_left hj] using hc⟩

def finiteBottomTuple (N m j : ℕ) (hj : j ≤ m)
    (T : FiniteTableau (finiteAugShape m j) N) : Fin j → Fin N :=
  fun c => ⟨T.1 m c.val, T.2 m c.val (bottom_cell_mem m j c.val hj c.isLt)⟩

theorem finiteAugTableau_bottom_ge (N m j : ℕ) (hj : j ≤ m)
    (T : FiniteTableau (finiteAugShape m j) N) (c : Fin j) :
    m ≤ (finiteBottomTuple N m j hj T c).val :=
  tableau_entry_ge_row T.1 (bottom_cell_mem m j c.val hj c.isLt)

#assert_trust kernel finiteAugTableau_bottom_ge
#print axioms finiteAugTableau_bottom_ge

end NLA.Proofs.MF03
