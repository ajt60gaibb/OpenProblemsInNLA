/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

The restricted labeled matching injection for FR-12, with AI-agent assistance.
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
import NLA.FR12.Semantics

set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
namespace NLA.FR12

@[simp] theorem doubling_top_top {m : ℕ} (A B : Mat m) (σ : Equiv.Perm (Fin m))
    (i j : Fin m) :
    doublingMatrix A B σ (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) =
      A i j := by
  simp only [doublingMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

@[simp] theorem doubling_top_bottom {m : ℕ} (A B : Mat m) (σ : Equiv.Perm (Fin m))
    (i j : Fin m) :
    doublingMatrix A B σ (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) =
      B i j := by
  simp only [doublingMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]

@[simp] theorem doubling_bottom_top {m : ℕ} (A B : Mat m) (σ : Equiv.Perm (Fin m))
    (i j : Fin m) :
    doublingMatrix A B σ (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) =
      A (σ i) j := by
  simp only [doublingMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, id_eq]

@[simp] theorem doubling_bottom_bottom {m : ℕ} (A B : Mat m) (σ : Equiv.Perm (Fin m))
    (i j : Fin m) :
    doublingMatrix A B σ (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) =
      -B (σ i) j := by
  simp only [doublingMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, id_eq]

theorem doubling_signs {m : ℕ} (A B : Mat m) (hA : IsRealHadamard A)
    (hB : IsRealHadamard B) (σ : Equiv.Perm (Fin m)) :
    ∀ i j, doublingMatrix A B σ i j = 1 ∨ doublingMatrix A B σ i j = -1 := by
  intro i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa only [doubling_top_top] using hA.1 i j
    | inr j => simpa only [doubling_top_bottom] using hB.1 i j
  | inr i =>
    cases j with
    | inl j => simpa only [doubling_bottom_top] using hA.1 (σ i) j
    | inr j =>
      rw [doubling_bottom_bottom]
      rcases hB.1 (σ i) j with h | h
      · exact Or.inr (by rw [h])
      · exact Or.inl (by rw [h]; ring)

theorem doubling_row_inner {m : ℕ} (A B : Mat m) (hA : IsRealHadamard A)
    (hB : IsRealHadamard B) (σ : Equiv.Perm (Fin m)) (i j : Fin (m + m)) :
    (∑ k, doublingMatrix A B σ i k * doublingMatrix A B σ j k) =
      if i = j then ((m + m : ℕ) : ℝ) else 0 := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [← Equiv.sum_comp (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m))]
  cases i <;> cases j <;>
    simp only [Fintype.sum_sum_type, doubling_top_top, doubling_top_bottom,
      doubling_bottom_top, doubling_bottom_bottom, mul_neg, neg_mul, neg_neg,
      Finset.sum_neg_distrib, row_inner A hA, row_inner B hB, Equiv.apply_eq_iff_eq,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, ite_false,
      Nat.cast_add] <;> split_ifs <;> ring

theorem doubling_hadamard {m : ℕ} (A B : Mat m) (hA : IsRealHadamard A)
    (hB : IsRealHadamard B) (σ : Equiv.Perm (Fin m)) :
    IsRealHadamard (doublingMatrix A B σ) := by
  refine ⟨doubling_signs A B hA hB σ, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply] using doubling_row_inner A B hA hB σ i j

theorem doubling_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (doublingMap m) := by
  rintro ⟨A, B, σ⟩ ⟨A', B', σ'⟩ h
  have hA : A = A' := by
    apply Subtype.ext
    ext i j
    have he := congrArg (fun M : Mat (m + m) =>
      M (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))) h
    simpa only [doublingMap, doubling_top_top] using he
  have hB : B = B' := by
    apply Subtype.ext
    ext i j
    have he := congrArg (fun M : Mat (m + m) =>
      M (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) h
    simpa only [doublingMap, doubling_top_bottom] using he
  subst A'
  subst B'
  have hs : σ = σ' := by
    apply Equiv.ext
    intro i
    apply rows_injective hm A.val A.property
    ext j
    have he := congrArg (fun M : Mat (m + m) =>
      M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j))) h
    simpa only [doublingMap, doubling_bottom_top] using he
  subst σ'
  rfl

theorem injective_doubling_proved (m : ℕ) (hm : 1 ≤ m) :
    (∀ x : HadamardMatrices m × HadamardMatrices m × Equiv.Perm (Fin m),
      IsRealHadamard (doublingMap m x)) ∧ Function.Injective (doublingMap m) := by
  refine ⟨?_, doubling_injective m hm⟩
  rintro ⟨A, B, σ⟩
  exact doubling_hadamard A.val B.val A.property B.property σ

theorem factorial_doubling_proved (m : ℕ) (hm : 1 ≤ m) :
    m.factorial * hadamardCount m ^ 2 ≤ hadamardCount (2 * m) := by
  let f : HadamardMatrices m × HadamardMatrices m × Equiv.Perm (Fin m) →
      HadamardMatrices (m + m) :=
    fun x => ⟨doublingMap m x, (injective_doubling_proved m hm).1 x⟩
  have hf : Function.Injective f := by
    intro x y h
    exact doubling_injective m hm (congrArg Subtype.val h)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_prod,
    Nat.card_eq_fintype_card (α := Equiv.Perm (Fin m)), Fintype.card_perm,
    Fintype.card_fin] at hc
  rw [two_mul]
  simpa only [hadamardCount, pow_two, mul_comm, mul_left_comm, mul_assoc] using hc

end NLA.FR12
