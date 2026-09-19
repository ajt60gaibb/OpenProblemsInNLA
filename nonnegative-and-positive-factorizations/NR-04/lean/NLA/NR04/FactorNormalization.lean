/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

The actual normalization-to-hull bridge for Matthew J. Colbrook's NR-04 proof,
University of Cambridge. Its convex weights are columnMass(W,r)*H(r,j)/columnMass(M,j).
When a W column is zero its weight is zero, so the arbitrary replacement
normalization has no effect on the represented column of M.
-/
import NLA.NR04.ColumnNormalization
import Mathlib.Analysis.Convex.Combination
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Classical

namespace NLA.NR04

theorem normalized_factor_column_containment {m n k : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ)
    (W : Matrix (Fin m) (Fin k) ℝ) (H : Matrix (Fin k) (Fin n) ℝ)
    (hW : EntrywiseNonnegative W) (hH : EntrywiseNonnegative H)
    (hWH : W * H = M) (hs : ∀ j, 0 < columnMass M j) (r : Fin k) :
    columnSet (columnNormalized M) ⊆ columnHull (filledColumnNormalized W r) := by
  rintro _ ⟨j, rfl⟩
  let c : Fin k → ℝ := fun l => columnMass W l * H l j / columnMass M j
  have hc (l : Fin k) : 0 ≤ c l :=
    div_nonneg (mul_nonneg (columnMass_nonnegative W hW l) (hH l j)) (hs j).le
  have hsum : ∑ l, c l = 1 := by
    dsimp only [c]
    rw [← Finset.sum_div, ← columnMass_mul, hWH]
    exact div_self (ne_of_gt (hs j))
  have hrep : (∑ l, c l • (fun i => filledColumnNormalized W r i l)) =
      (fun i => columnNormalized M i j) := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ l, c l * filledColumnNormalized W r i l) = M i j / columnMass M j
    calc
      (∑ l, c l * filledColumnNormalized W r i l) =
          ∑ l, W i l * H l j / columnMass M j := by
        apply Finset.sum_congr rfl
        intro l _
        dsimp only [c]
        calc
          columnMass W l * H l j / columnMass M j * filledColumnNormalized W r i l =
              (columnMass W l * filledColumnNormalized W r i l) * H l j /
                columnMass M j := by ring
          _ = W i l * H l j / columnMass M j := by
            rw [filledColumnNormalized_mass_mul W hW r l i]
      _ = M i j / columnMass M j := by
        rw [← Finset.sum_div]
        have hp := congrFun (congrFun hWH i) j
        change (∑ l, W i l * H l j) = M i j at hp
        rw [hp]
  change (fun i => columnNormalized M i j) ∈ columnHull (filledColumnNormalized W r)
  have hmem : (∑ l, c l • (fun i => filledColumnNormalized W r i l)) ∈
      columnHull (filledColumnNormalized W r) :=
    (convex_convexHull ℝ (columnSet (filledColumnNormalized W r))).sum_mem
      (fun l _ => hc l) hsum
      (fun l _ => subset_convexHull ℝ _ ⟨l, rfl⟩)
  exact hrep ▸ hmem

theorem sign_pattern_columnMass_positive {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (hN : 2 ≤ N)
    (hdiag : ∀ i, M i i = 0) (hoff : ∀ i j, i ≠ j → 0 < M i j) :
    EntrywiseNonnegative M ∧ ∀ j, 0 < columnMass M j := by
  have hM : EntrywiseNonnegative M := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact (hdiag i).symm.le
    · exact (hoff i j hij).le
  refine ⟨hM, ?_⟩
  intro j
  obtain ⟨i, hi⟩ : ∃ i : Fin N, i ≠ j := by
    by_cases hj : j.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro he
      have hval := congrArg Fin.val he
      dsimp at hval
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro he
      exact hj (congrArg Fin.val he).symm
  have hsingle : M i j ≤ columnMass M j :=
    Finset.single_le_sum (fun l _ => hM l j) (Finset.mem_univ i)
  exact lt_of_lt_of_le (hoff i j hi) hsingle

#print axioms normalized_factor_column_containment
#print axioms sign_pattern_columnMass_positive
#assert_trust kernel normalized_factor_column_containment
#assert_trust kernel sign_pattern_columnMass_positive

end NLA.NR04
