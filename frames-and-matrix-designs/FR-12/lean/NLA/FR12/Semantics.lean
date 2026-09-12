/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact labeled-matrix semantics for FR-12. Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena, USA.
Substantial AI-agent assistance; statement approvals precede this implementation.
-/
import NLA.FR12.Definitions
import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section

namespace NLA.FR12

/-- Encode every labeled sign entry in a Boolean matrix. The Gram constraint
only restricts this finite type further. -/
instance finiteHadamardMatrices (n : ℕ) : Finite (HadamardMatrices n) := by
  let encode : HadamardMatrices n → Matrix (Fin n) (Fin n) Bool :=
    fun A i j => decide (A.val i j = 1)
  apply Finite.of_injective encode
  intro A B h
  apply Subtype.ext
  ext i j
  have hij := congrFun (congrFun h i) j
  dsimp only [encode] at hij
  rcases A.property.1 i j with ha | ha <;>
    rcases B.property.1 i j with hb | hb <;>
    first | exact ha.trans hb.symm | norm_num [ha, hb] at hij

theorem isRealHadamard_iff_mathlib {n : ℕ} (hn : 1 ≤ n) (A : Mat n) :
    IsRealHadamard A ↔ A.IsHadamard := by
  constructor
  · intro hA
    apply Matrix.IsHadamard.of_mul_conjTranspose
    · intro i j
      exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hA.1 i j)
    · simpa using hA.2
    · apply isRegular_iff_ne_zero.mpr
      simp only [Fintype.card_fin, Nat.cast_ne_zero]
      omega
  · intro hA
    refine ⟨fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i j), ?_⟩
    simpa using hA.mul_conjTranspose

theorem counting_semantics_proved (n : ℕ) :
    Finite (HadamardMatrices n) ∧
    (∀ (_hn : 1 ≤ n) (A : Mat n), IsRealHadamard A ↔ A.IsHadamard) :=
  ⟨inferInstance, fun hn A => isRealHadamard_iff_mathlib hn A⟩

/-- Actual row inner products, with the full original real Gram normalization. -/
theorem row_inner {n : ℕ} (A : Mat n) (hA : IsRealHadamard A) (i j : Fin n) :
    (∑ k, A i k * A j k) = if i = j then (n : ℝ) else 0 := by
  have h := congrArg (fun M : Mat n => M i j) hA.2
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply] using h

theorem rows_injective {n : ℕ} (hn : 1 ≤ n) (A : Mat n) (hA : IsRealHadamard A) :
    Function.Injective A := by
  intro i j hij
  by_contra hne
  have hd := row_inner A hA i i
  have ho := row_inner A hA i j
  have he : (∑ k, A i k * A i k) = ∑ k, A i k * A j k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [congrFun hij k]
  simp only [ite_true, if_neg hne] at hd ho
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  linarith

end NLA.FR12
