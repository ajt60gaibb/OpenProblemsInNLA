import NLA.Proofs.MF03.FiniteRectDetTableau
import NLA.Proofs.MF03.FiniteTableauCanonical

/-!
A fixed positive canonical tableau weight lies below every sufficiently
large original finite rectangular determinant, hence below its limit.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Filter
open scoped BigOperators

namespace NLA.Proofs.MF03

/-- The exact original weight of the tableau whose row `r` has label `r`. -/
noncomputable def canonicalRectWeight (m : ℕ) : ℝ :=
  ∏ r ∈ Finset.range m, ∏ _c ∈ Finset.range m, cosineFactor (r + 1)

private theorem cosineFactor_row_pos (k : ℕ) :
    0 < cosineFactor (k + 1) := by
  unfold cosineFactor
  have hk : (0 : ℝ) < (((k + 1 : ℕ) : ℝ) - 1 / 2) := by
    have hnonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    push_cast
    linarith
  positivity

/-- The canonical rectangular weight is positive, including the empty
rectangle where it equals one. -/
theorem canonicalRectWeight_pos (m : ℕ) :
    0 < canonicalRectWeight m := by
  unfold canonicalRectWeight
  apply Finset.prod_pos
  intro r hr
  apply Finset.prod_pos
  intro c hc
  exact cosineFactor_row_pos r

private theorem finiteRectWeight_nonneg_all (m : ℕ) (T : ℕ → ℕ → ℕ) :
    0 ≤ finiteRectWeight m T := by
  unfold finiteRectWeight
  apply Finset.prod_nonneg
  intro r hr
  apply Finset.prod_nonneg
  intro c hc
  exact (cosineFactor_row_pos (T r c)).le

/-- The already constructed canonical tableau has exactly the fixed
original row-label weight, for every cutoff `N≥m`. -/
theorem finiteRectWeight_canonical (N m : ℕ) (hm : m ≤ N) :
    finiteRectWeight m (canonicalRectTableau N m hm).1 =
      canonicalRectWeight m := by
  unfold finiteRectWeight canonicalRectWeight
  apply Finset.prod_congr rfl
  intro r hr
  apply Finset.prod_congr rfl
  intro c hc
  have hcell : (r, c) ∈ finiteRectShape m :=
    (mem_finiteRectShape m r c).mpr
      ⟨Finset.mem_range.mp hr, Finset.mem_range.mp hc⟩
  have hentry : (canonicalRectTableau N m hm).1 r c = r := by
    change (if (r, c) ∈ finiteRectShape m then r else 0) = r
    simp [hcell]
  rw [hentry]

/-- The fixed positive weight is a uniform lower bound for every
original finite rectangular determinant with `N≥m`. -/
theorem canonicalRectWeight_le_finiteRectDet
    (N m : ℕ) (hm : m ≤ N) :
    canonicalRectWeight m ≤ finiteCosineRectDet N m := by
  rw [finiteCosineRectDet_eq_rectTableauSum]
  unfold finiteRectTableauSum
  calc
    canonicalRectWeight m =
        finiteRectWeight m (canonicalRectTableau N m hm).1 :=
      (finiteRectWeight_canonical N m hm).symm
    _ ≤ ∑ T : FiniteTableau (finiteRectShape m) N,
          finiteRectWeight m T.1 := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (fun T _ => finiteRectWeight_nonneg_all m T.1)
        (Finset.mem_univ (canonicalRectTableau N m hm))

/-- The original infinite rectangular elementary-coefficient determinant
is strictly positive in every order, including order zero. -/
theorem cosineRectDet_pos (m : ℕ) :
    0 < cosineRectDet m := by
  have hlower : canonicalRectWeight m ≤ cosineRectDet m := by
    apply ge_of_tendsto (finiteCosineRectDet_tendsto m)
    exact eventually_atTop.mpr
      ⟨m, fun N hN => canonicalRectWeight_le_finiteRectDet N m hN⟩
  exact (canonicalRectWeight_pos m).trans_le hlower

#assert_trust kernel canonicalRectWeight_pos
#assert_trust kernel finiteRectWeight_canonical
#assert_trust kernel canonicalRectWeight_le_finiteRectDet
#assert_trust kernel cosineRectDet_pos
#print axioms cosineRectDet_pos

end NLA.Proofs.MF03
