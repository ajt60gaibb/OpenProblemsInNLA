/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Actual column normalization for Matthew J. Colbrook's NR-04 proof,
University of Cambridge. Zero columns are treated explicitly. Replacing an
inactive column by an existing normalized column preserves the generator
span and permits the original inner dimension to remain unchanged.
-/
import NLA.NR04.Definitions
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Classical

namespace NLA.NR04

def columnMass {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : ℝ :=
  ∑ i, A i j

def columnNormalized {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ := fun i j => A i j / columnMass A j

def filledColumnNormalized {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if columnMass A j = 0 then columnNormalized A i r
    else columnNormalized A i j

theorem columnMass_nonnegative {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : EntrywiseNonnegative A) (j : Fin n) : 0 ≤ columnMass A j := by
  exact Finset.sum_nonneg (fun i _ => hA i j)

theorem column_zero_of_mass_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : EntrywiseNonnegative A) (j : Fin n) (hj : columnMass A j = 0) :
    ∀ i, A i j = 0 := by
  intro i
  apply le_antisymm _ (hA i j)
  have h : A i j ≤ columnMass A j :=
    Finset.single_le_sum (fun l _ => hA l j) (Finset.mem_univ i)
  exact hj ▸ h

theorem columnMass_mul {m n k : ℕ}
    (W : Matrix (Fin m) (Fin k) ℝ) (H : Matrix (Fin k) (Fin n) ℝ) (j : Fin n) :
    columnMass (W * H) j = ∑ r, columnMass W r * H r j := by
  simp only [columnMass, Matrix.mul_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun r _ => (Finset.sum_mul _ _ _).symm)

theorem columnNormalized_stochastic {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : EntrywiseNonnegative A)
    (hs : ∀ j, 0 < columnMass A j) : ColumnStochastic (columnNormalized A) := by
  constructor
  · intro i j
    exact div_nonneg (hA i j) (le_of_lt (hs j))
  · intro j
    change (∑ i, A i j / columnMass A j) = 1
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (hs j))

theorem columnNormalized_rank {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hs : ∀ j, columnMass A j ≠ 0) :
    (columnNormalized A).rank = A.rank := by
  have hforward : columnNormalized A = A * Matrix.diagonal (fun j => (columnMass A j)⁻¹) := by
    ext i j
    simp [columnNormalized, div_eq_mul_inv]
  have hback : A = columnNormalized A * Matrix.diagonal (columnMass A) := by
    ext i j
    simp [columnNormalized, div_eq_mul_inv, hs]
  apply le_antisymm
  · rw [hforward]
    exact Matrix.rank_mul_le_left _ _
  · calc
      A.rank = (columnNormalized A * Matrix.diagonal (columnMass A)).rank :=
        congrArg Matrix.rank hback
      _ ≤ (columnNormalized A).rank := Matrix.rank_mul_le_left _ _

theorem filledColumnNormalized_stochastic {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : EntrywiseNonnegative A)
    (r : Fin n) (hr : 0 < columnMass A r) :
    ColumnStochastic (filledColumnNormalized A r) := by
  have hpos (j : Fin n) (hj : columnMass A j ≠ 0) : 0 < columnMass A j :=
    lt_of_le_of_ne (columnMass_nonnegative A hA j) (Ne.symm hj)
  constructor
  · intro i j
    by_cases hj : columnMass A j = 0
    · exact (show 0 ≤ A i r / columnMass A r from
        div_nonneg (hA i r) hr.le).trans_eq (by simp [filledColumnNormalized, hj, columnNormalized])
    · exact (show 0 ≤ A i j / columnMass A j from
        div_nonneg (hA i j) (hpos j hj).le).trans_eq
          (by simp [filledColumnNormalized, hj, columnNormalized])
  · intro j
    by_cases hj : columnMass A j = 0
    · simp only [filledColumnNormalized, if_pos hj, columnNormalized]
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hr)
    · simp only [filledColumnNormalized, if_neg hj, columnNormalized]
      rw [← Finset.sum_div]
      exact div_self hj

theorem filledColumnNormalized_rank_le {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n) :
    (filledColumnNormalized A r).rank ≤ A.rank := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  by_cases hj : columnMass A j = 0
  · have hvec : (filledColumnNormalized A r).col j =
        (columnMass A r)⁻¹ • A.col r := by
      ext i
      simp [Matrix.col_apply, filledColumnNormalized, hj, columnNormalized,
        div_eq_mul_inv, mul_comm]
    rw [hvec]
    exact (Submodule.span ℝ (Set.range A.col)).smul_mem
      (columnMass A r)⁻¹ (Submodule.subset_span (Set.mem_range_self r))
  · have hvec : (filledColumnNormalized A r).col j =
        (columnMass A j)⁻¹ • A.col j := by
      ext i
      simp [Matrix.col_apply, filledColumnNormalized, hj, columnNormalized,
        div_eq_mul_inv, mul_comm]
    rw [hvec]
    exact (Submodule.span ℝ (Set.range A.col)).smul_mem
      (columnMass A j)⁻¹ (Submodule.subset_span (Set.mem_range_self j))

theorem filledColumnNormalized_mass_mul {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : EntrywiseNonnegative A)
    (r j : Fin n) (i : Fin m) :
    columnMass A j * filledColumnNormalized A r i j = A i j := by
  by_cases hj : columnMass A j = 0
  · rw [hj, zero_mul, column_zero_of_mass_zero A hA j hj i]
  · simp only [filledColumnNormalized, if_neg hj, columnNormalized]
    field_simp [hj]

#print axioms columnMass_nonnegative
#print axioms column_zero_of_mass_zero
#print axioms columnMass_mul
#print axioms columnNormalized_stochastic
#print axioms columnNormalized_rank
#print axioms filledColumnNormalized_stochastic
#print axioms filledColumnNormalized_rank_le
#print axioms filledColumnNormalized_mass_mul
#assert_trust kernel columnMass_nonnegative
#assert_trust kernel column_zero_of_mass_zero
#assert_trust kernel columnMass_mul
#assert_trust kernel columnNormalized_stochastic
#assert_trust kernel columnNormalized_rank
#assert_trust kernel filledColumnNormalized_stochastic
#assert_trust kernel filledColumnNormalized_rank_le
#assert_trust kernel filledColumnNormalized_mass_mul

end NLA.NR04
