import NLA.Proofs.MF03.FiniteTableauTailBound

/-!
Explicit row-constant semistandard tableaux for the finite rectangle and its
augmented bottom row. These witness positive finite tableau sums; determinant
identities and infinite limits remain separate obligations.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

private def rowLabelTableau (μ : YoungDiagram) :
    SemistandardYoungTableau μ where
  entry r c := if (r, c) ∈ μ then r else 0
  row_weak' := by
    intro r c₁ c₂ hlt hcell
    have hcell₁ : (r, c₁) ∈ μ :=
      μ.up_left_mem le_rfl (Nat.le_of_lt hlt) hcell
    simp [hcell, hcell₁]
  col_strict' := by
    intro r₁ r₂ c hlt hcell
    have hcell₁ : (r₁, c) ∈ μ :=
      μ.up_left_mem (Nat.le_of_lt hlt) le_rfl hcell
    simpa [hcell, hcell₁] using hlt
  zeros' := by
    intro r c hnot
    simp [hnot]

/-- The rectangular tableau whose row `r` has constant zero-based label `r`. -/
def canonicalRectTableau (N m : ℕ) (hm : m ≤ N) :
    FiniteTableau (finiteRectShape m) N := by
  refine ⟨rowLabelTableau (finiteRectShape m), ?_⟩
  intro r c hcell
  have hr : r < m := ((mem_finiteRectShape m r c).mp hcell).1
  change (if (r, c) ∈ finiteRectShape m then r else 0) < N
  simpa [hcell] using lt_of_lt_of_le hr hm

/-- The augmented tableau whose row `r`, including the extra row, has label `r`. -/
def canonicalAugTableau (N m j : ℕ) (_hj : j ≤ m) (hN : m < N) :
    FiniteTableau (finiteAugShape m j) N := by
  refine ⟨rowLabelTableau (finiteAugShape m j), ?_⟩
  intro r c hcell
  have hr : r ≤ m := by
    rcases (mem_finiteAugShape m j r c).mp hcell with hrect | hbottom
    · exact Nat.le_of_lt hrect.1
    · exact hbottom.1.le
  change (if (r, c) ∈ finiteAugShape m j then r else 0) < N
  simpa [hcell] using lt_of_le_of_lt hr hN

private theorem cosineFactor_tail_pos (k : ℕ) :
    0 < cosineFactor (k + 1) := by
  unfold cosineFactor
  have hk : (0 : ℝ) < (((k + 1 : ℕ) : ℝ) - 1 / 2) := by
    have hnonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    push_cast
    linarith
  positivity

private theorem finiteRectWeight_pos (m : ℕ) (T : ℕ → ℕ → ℕ) :
    0 < finiteRectWeight m T := by
  unfold finiteRectWeight
  apply Finset.prod_pos
  intro r hr
  apply Finset.prod_pos
  intro c hc
  exact cosineFactor_tail_pos (T r c)

private theorem finiteBottomWeight_pos (j m : ℕ) (T : ℕ → ℕ → ℕ) :
    0 < finiteBottomWeight j m T := by
  unfold finiteBottomWeight
  apply Finset.prod_pos
  intro c hc
  exact cosineFactor_tail_pos (T m c)

/-- The finite rectangular weighted tableau sum is positive at `N ≥ m`. -/
theorem finiteRectTableauSum_pos (N m : ℕ) (hm : m ≤ N) :
    0 < finiteRectTableauSum N m := by
  unfold finiteRectTableauSum
  apply Finset.sum_pos'
  · intro T hT
    exact (finiteRectWeight_pos m T.1).le
  · exact ⟨canonicalRectTableau N m hm, Finset.mem_univ _,
      finiteRectWeight_pos m _⟩

/-- The finite augmented weighted tableau sum is positive at `N>m`. -/
theorem finiteAugTableauSum_pos (N m j : ℕ) (hj : j ≤ m) (hN : m < N) :
    0 < finiteAugTableauSum N m j := by
  unfold finiteAugTableauSum
  apply Finset.sum_pos'
  · intro T hT
    exact mul_nonneg (finiteRectWeight_pos m T.1).le
      (finiteBottomWeight_pos j m T.1).le
  · refine ⟨canonicalAugTableau N m j hj hN, Finset.mem_univ _, ?_⟩
    exact mul_pos (finiteRectWeight_pos m _)
      (finiteBottomWeight_pos j m _)

#assert_trust kernel finiteRectTableauSum_pos
#assert_trust kernel finiteAugTableauSum_pos

end NLA.Proofs.MF03
