/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Homogeneous quadratic forms in an arbitrary selected ordered eigenbasis.
The finite-dimensional kernel argument follows the same standard Mathlib
dimension API used in the campaign's MI-06 proof.
-/
import NLA.RA08.Witness
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
open Matrix
noncomputable section
namespace NLA.RA08

theorem real_length_positive {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  have hne : x ⬝ᵥ x ≠ 0 := fun h => hx (dotProduct_self_eq_zero.mp h)
  exact lt_of_le_of_ne (real_length_nonneg x) (Ne.symm hne)

theorem rectangular_kernel {m n : ℕ} (hnm : n < m) (M : Matrix (Fin n) (Fin m) ℝ) :
    ∃ x : Fin m → ℝ, x ≠ 0 ∧ M *ᵥ x = 0 := by
  let F : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) := M.mulVecLin
  have hF : ¬ Function.Injective F := by
    intro h
    have hd := LinearMap.finrank_le_finrank_of_injective h
    have hmn : m ≤ n := by simpa [Module.finrank_fintype_fun_eq_card] using hd
    exact (Nat.not_le_of_gt hnm) hmn
  obtain ⟨x, hx⟩ := not_forall.mp hF
  obtain ⟨y, hy⟩ := not_forall.mp hx
  obtain ⟨hxy, hne⟩ := Classical.not_imp.mp hy
  have hz : F (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact ⟨x - y, sub_ne_zero.mpr hne, hz⟩

theorem basis_transpose_mul {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) :
    (d.orthogonal : RealMatrix n).transpose * (d.orthogonal : RealMatrix n) = 1 := by
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial] using Unitary.coe_star_mul_self d.orthogonal

theorem basis_length {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (z : Fin n → ℝ) :
    ((d.orthogonal : RealMatrix n) *ᵥ z) ⬝ᵥ ((d.orthogonal : RealMatrix n) *ᵥ z) = z ⬝ᵥ z := by
  have h := real_gram_quadratic (d.orthogonal : RealMatrix n) z
  rw [basis_transpose_mul, one_mulVec] at h
  exact h.symm

theorem basis_nonzero {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (z : Fin n → ℝ) (hz : z ≠ 0) : (d.orthogonal : RealMatrix n) *ᵥ z ≠ 0 := by
  intro h
  have hd := basis_length d z
  rw [h, zero_dotProduct] at hd
  exact hz (dotProduct_self_eq_zero.mp hd.symm)

theorem real_conjugated_quadratic {n : ℕ} (A Q : RealMatrix n) (z : Fin n → ℝ) :
    z ⬝ᵥ ((Q.transpose * A * Q) *ᵥ z) =
      (Q *ᵥ z) ⬝ᵥ (A *ᵥ (Q *ᵥ z)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem basis_conjugated_matrix {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) :
    (d.orthogonal : RealMatrix n).transpose * A * (d.orthogonal : RealMatrix n) =
      diagonal d.eigenvalues := by
  conv_lhs =>
    arg 1
    arg 2
    rw [d.reconstruct]
  calc
    _ = ((d.orthogonal : RealMatrix n).transpose * (d.orthogonal : RealMatrix n)) *
        diagonal d.eigenvalues *
        ((d.orthogonal : RealMatrix n).transpose * (d.orthogonal : RealMatrix n)) := by
          simp only [mul_assoc]
    _ = _ := by rw [basis_transpose_mul, one_mul, mul_one]

theorem basis_quadratic {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (z : Fin n → ℝ) :
    ((d.orthogonal : RealMatrix n) *ᵥ z) ⬝ᵥ
        (A *ᵥ ((d.orthogonal : RealMatrix n) *ᵥ z)) =
      ∑ i, d.eigenvalues i * (z i) ^ 2 := by
  rw [← real_conjugated_quadratic, basis_conjugated_matrix]
  simp only [dotProduct, mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem basis_rayleigh_lower {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (z : Fin n → ℝ) (r : ℝ) (h : ∀ i, z i ≠ 0 → r ≤ d.eigenvalues i) :
    r * (((d.orthogonal : RealMatrix n) *ᵥ z) ⬝ᵥ ((d.orthogonal : RealMatrix n) *ᵥ z)) ≤
      ((d.orthogonal : RealMatrix n) *ᵥ z) ⬝ᵥ
        (A *ᵥ ((d.orthogonal : RealMatrix n) *ᵥ z)) := by
  rw [basis_length, basis_quadratic]
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hz : z i = 0
  · simp [hz]
  · simpa only [pow_two] using mul_le_mul_of_nonneg_right (h i hz) (mul_self_nonneg (z i))

theorem basis_rayleigh_upper {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (z : Fin n → ℝ) (r : ℝ) (h : ∀ i, z i ≠ 0 → d.eigenvalues i ≤ r) :
    ((d.orthogonal : RealMatrix n) *ᵥ z) ⬝ᵥ
        (A *ᵥ ((d.orthogonal : RealMatrix n) *ᵥ z)) ≤
      r * (((d.orthogonal : RealMatrix n) *ᵥ z) ⬝ᵥ ((d.orthogonal : RealMatrix n) *ᵥ z)) := by
  rw [basis_length, basis_quadratic]
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hz : z i = 0
  · simp [hz]
  · simpa only [pow_two] using mul_le_mul_of_nonneg_right (h i hz) (mul_self_nonneg (z i))

#assert_trust kernel rectangular_kernel
#assert_trust kernel basis_quadratic
#assert_trust kernel basis_rayleigh_lower
#assert_trust kernel basis_rayleigh_upper
#print axioms rectangular_kernel
#print axioms basis_quadratic
#print axioms basis_rayleigh_lower
#print axioms basis_rayleigh_upper

end NLA.RA08
