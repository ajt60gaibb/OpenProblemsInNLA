/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

The fourth eigenvalue for every allowed ordered eigenbasis. Two rectangular
kernel arguments replace any assumed min-max or perturbation theorem.
-/
import NLA.RA08.Basis
import NLA.RA08.Location

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
open Matrix
noncomputable section
namespace NLA.RA08

def frontCoefficients (c : Fin 4 → ℝ) : Fin 6 → ℝ := ![c 0, c 1, c 2, c 3, 0, 0]
def backCoefficients (c : Fin 3 → ℝ) : Fin 6 → ℝ := ![0, 0, 0, c 0, c 1, c 2]

theorem front_nonzero (c : Fin 4 → ℝ) (hc : c ≠ 0) : frontCoefficients c ≠ 0 := by
  intro h
  apply hc
  ext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2
  · exact congrFun h 3

theorem back_nonzero (c : Fin 3 → ℝ) (hc : c ≠ 0) : backCoefficients c ≠ 0 := by
  intro h
  apply hc
  ext i
  fin_cases i
  · exact congrFun h 3
  · exact congrFun h 4
  · exact congrFun h 5

theorem front_kernel (Q : RealMatrix 6) :
    ∃ c : Fin 4 → ℝ, c ≠ 0 ∧ (Q *ᵥ frontCoefficients c) 0 = 0 ∧
      (Q *ᵥ frontCoefficients c) 1 = 0 ∧ (Q *ᵥ frontCoefficients c) 2 = 0 := by
  let M : Matrix (Fin 3) (Fin 4) ℝ :=
    !![Q 0 0, Q 0 1, Q 0 2, Q 0 3;
       Q 1 0, Q 1 1, Q 1 2, Q 1 3;
       Q 2 0, Q 2 1, Q 2 2, Q 2 3]
  obtain ⟨c, hc, he⟩ := rectangular_kernel (by decide : 3 < 4) M
  refine ⟨c, hc, ?_, ?_, ?_⟩
  · simpa [M, frontCoefficients, mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using congrFun he 0
  · simpa [M, frontCoefficients, mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using congrFun he 1
  · simpa [M, frontCoefficients, mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using congrFun he 2

theorem back_kernel (Q : RealMatrix 6) :
    ∃ c : Fin 3 → ℝ, c ≠ 0 ∧ (Q *ᵥ backCoefficients c) 3 = 0 ∧
      (Q *ᵥ backCoefficients c) 4 = 0 := by
  let M : Matrix (Fin 2) (Fin 3) ℝ :=
    !![Q 3 3, Q 3 4, Q 3 5; Q 4 3, Q 4 4, Q 4 5]
  obtain ⟨c, hc, he⟩ := rectangular_kernel (by decide : 2 < 3) M
  refine ⟨c, hc, ?_, ?_⟩
  · simpa [M, backCoefficients, mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using congrFun he 0
  · simpa [M, backCoefficients, mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using congrFun he 1

theorem fourth_le_of_three_coordinate_kernel {A : RealMatrix 6}
    (d : OrderedSpectralData A) (r : ℝ)
    (h : ∀ x : Fin 6 → ℝ, x 0 = 0 → x 1 = 0 → x 2 = 0 →
      x ⬝ᵥ (A *ᵥ x) ≤ r * (x ⬝ᵥ x)) : d.eigenvalues 3 ≤ r := by
  by_contra hn
  have hr : r < d.eigenvalues 3 := lt_of_not_ge hn
  obtain ⟨c, hc, h0, h1, h2⟩ := front_kernel (d.orthogonal : RealMatrix 6)
  let z := frontCoefficients c
  let x := (d.orthogonal : RealMatrix 6) *ᵥ z
  have hx : x ≠ 0 := basis_nonzero d z (front_nonzero c hc)
  have hpos := real_length_positive x hx
  have hu := h x h0 h1 h2
  have hl := basis_rayleigh_lower d z (d.eigenvalues 3) (by
    intro i hi
    fin_cases i
    · exact d.decreasing (by decide)
    · exact d.decreasing (by decide)
    · exact d.decreasing (by decide)
    · exact le_rfl
    · simp [z, frontCoefficients] at hi
    · simp [z, frontCoefficients] at hi)
  change d.eigenvalues 3 * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) at hl
  have hp := mul_pos (sub_pos.mpr hr) hpos
  nlinarith

theorem fourth_ge_of_two_coordinate_kernel {A : RealMatrix 6}
    (d : OrderedSpectralData A) (r : ℝ)
    (h : ∀ x : Fin 6 → ℝ, x 3 = 0 → x 4 = 0 →
      r * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) : r ≤ d.eigenvalues 3 := by
  by_contra hn
  have hr : d.eigenvalues 3 < r := lt_of_not_ge hn
  obtain ⟨c, hc, h3, h4⟩ := back_kernel (d.orthogonal : RealMatrix 6)
  let z := backCoefficients c
  let x := (d.orthogonal : RealMatrix 6) *ᵥ z
  have hx : x ≠ 0 := basis_nonzero d z (back_nonzero c hc)
  have hpos := real_length_positive x hx
  have hl := h x h3 h4
  have hu := basis_rayleigh_upper d z (d.eigenvalues 3) (by
    intro i hi
    fin_cases i
    · simp [z, backCoefficients] at hi
    · simp [z, backCoefficients] at hi
    · simp [z, backCoefficients] at hi
    · exact le_rfl
    · exact d.decreasing (by decide)
    · exact d.decreasing (by decide))
  change x ⬝ᵥ (A *ᵥ x) ≤ d.eigenvalues 3 * (x ⬝ᵥ x) at hu
  have hp := mul_pos (sub_pos.mpr hr) hpos
  nlinarith

theorem six_length (x : Fin 6 → ℝ) : x ⬝ᵥ x =
    (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 + (x 4) ^ 2 + (x 5) ^ 2 := by
  change x 0 * x 0 + (x 1 * x 1 + (x 2 * x 2 +
    (x 3 * x 3 + (x 4 * x 4 + (x 5 * x 5 + 0))))) = _
  ring

theorem single_sq_le_length {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (x i) ^ 2 ≤ x ⬝ᵥ x := by
  simpa only [pow_two, dotProduct] using Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => mul_self_nonneg (x j))
    (Finset.mem_univ i)

theorem witnessF_last_quadratic (x : Fin 6 → ℝ) : (x 5) ^ 2 ≤ x ⬝ᵥ (witnessF *ᵥ x) := by
  have hlast : (witnessF *ᵥ x) 5 = x 5 := by
    have hrow : witnessF 5 = ![0, 0, 0, 0, 0, 1] := by
      change witnessF ⟨5, by decide⟩ = _
      ext j
      fin_cases j <;> norm_num [witnessF]
    change witnessF 5 ⬝ᵥ x = x 5
    rw [hrow]
    norm_num [dotProduct, Fin.sum_univ_succ]
    rfl
  rw [witnessF_quadratic]
  have h := single_sq_le_length (witnessF *ᵥ x) 5
  rwa [hlast] at h

theorem witness_lower_on_four (x : Fin 6 → ℝ) (h3 : x 3 = 0) (h4 : x 4 = 0) :
    witnessT * (x ⬝ᵥ x) ≤ x ⬝ᵥ (witnessMatrix *ᵥ x) := by
  have hF := witnessF_last_quadratic x
  rw [witnessMatrix_quadratic, ← witnessF_quadratic, six_length, h3, h4]
  norm_num [witnessA, witnessB, witnessT]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

theorem witness_upper_on_three (x : Fin 6 → ℝ)
    (h0 : x 0 = 0) (h1 : x 1 = 0) (h2 : x 2 = 0) :
    x ⬝ᵥ (witnessMatrix *ᵥ x) ≤ witnessT * (x ⬝ᵥ x) := by
  rw [witnessMatrix_quadratic, ← witnessF_quadratic, h0, h1, h2]
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, zero_add]
  exact mul_le_mul_of_nonneg_left (witnessF_quadratic_le x) witnessT_pos.le

theorem witness_fourth (d : OrderedSpectralData witnessMatrix) : d.eigenvalues 3 = witnessT := by
  exact le_antisymm
    (fourth_le_of_three_coordinate_kernel d witnessT witness_upper_on_three)
    (fourth_ge_of_two_coordinate_kernel d witnessT witness_lower_on_four)

theorem approximation_fourth (d : OrderedSpectralData witnessApproximation) : d.eigenvalues 3 = 0 := by
  apply le_antisymm _ (d.nonnegative 3)
  apply fourth_le_of_three_coordinate_kernel d 0
  intro x h0 h1 h2
  rw [witnessApproximation_quadratic, h0, h1, h2]
  simp

#assert_trust kernel fourth_le_of_three_coordinate_kernel
#assert_trust kernel fourth_ge_of_two_coordinate_kernel
#assert_trust kernel witness_fourth
#assert_trust kernel approximation_fourth
#print axioms fourth_le_of_three_coordinate_kernel
#print axioms fourth_ge_of_two_coordinate_kernel
#print axioms witness_fourth
#print axioms approximation_fourth

end NLA.RA08
