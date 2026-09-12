/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: George Stepaniants

The exact all-k rank-one construction from Matthew J. Colbrook's MI-03 proof.
Formalization: Department of Computing and Mathematical Sciences, California
Institute of Technology, Pasadena, California, USA. AI-assisted.
-/
import NLA.MI03.Roots
import Mathlib.Tactic.FinCases

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI03

theorem outerProduct_star {n : ℕ} (u v : Fin n → ℂ) :
    (outerProduct u v).conjTranspose = outerProduct v u := by
  ext i j
  simp [outerProduct, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]

theorem outerProduct_mul {n : ℕ} (u v w z : Fin n → ℂ) :
    outerProduct u v * outerProduct w z =
      (∑ i, star (v i) * w i) • outerProduct u z := by
  ext i j
  simp only [outerProduct, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem outerProduct_posSemidef {n : ℕ} (v : Fin n → ℂ) :
    (outerProduct v v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

theorem firstVector_inner : (∑ i, star (firstVector i) * firstVector i) = 1 := by
  norm_num [firstVector, Fin.sum_univ_succ]

theorem witnessVector_inner (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    (∑ i, star (witnessVector k j i) * witnessVector k j i) = 1 := by
  simp only [witnessVector, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, map_mul, map_div₀, map_ofNat, Complex.star_def,
    Complex.conj_ofReal, map_one]
  have hr : rootOfUnity k ^ (j : ℕ) * (starRingEnd ℂ) (rootOfUnity k ^ (j : ℕ)) = 1 := by
    simpa only [Complex.star_def] using root_power_star k hk j
  have hs := sqrt_three_sq
  calc
    _ = (1 / 4 : ℂ) + (((Real.sqrt 3 : ℝ) : ℂ) ^ 2) / 4 *
        (rootOfUnity k ^ (j : ℕ) * (starRingEnd ℂ) (rootOfUnity k ^ (j : ℕ))) := by ring
    _ = 1 := by rw [hs, hr]; norm_num

theorem witnessVector_norm (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    ‖WithLp.toLp 2 (witnessVector k j)‖ = (1 : ℝ) := by
  have h := witnessVector_inner k hk j
  have he : ‖WithLp.toLp 2 (witnessVector k j)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hre := congrArg Complex.re h
    simpa only [Complex.re_sum, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re, ← Complex.sq_norm, Complex.one_re] using hre
  have hn := norm_nonneg (WithLp.toLp 2 (witnessVector k j))
  nlinarith

theorem witness_gram (k : ℕ) (j : Fin k) :
    (witness k j).conjTranspose * witness k j =
      outerProduct (witnessVector k j) (witnessVector k j) := by
  rw [witness, outerProduct_star, outerProduct_mul, firstVector_inner, one_smul]

theorem witnessModulus_idempotent (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    outerProduct (witnessVector k j) (witnessVector k j) *
      outerProduct (witnessVector k j) (witnessVector k j) =
      outerProduct (witnessVector k j) (witnessVector k j) := by
  rw [outerProduct_mul, witnessVector_inner k hk j, one_smul]

theorem witness_modulus (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    matrixModulus (witness k j) = outerProduct (witnessVector k j) (witnessVector k j) := by
  apply CFC.sqrt_unique
  · rw [witnessModulus_idempotent k hk j, witness_gram]
  · exact (outerProduct_posSemidef _).nonneg

theorem witness_reverse_gram (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    witness k j * (witness k j).conjTranspose = firstProjection := by
  rw [witness, outerProduct_star, outerProduct_mul, witnessVector_inner k hk j, one_smul]
  rfl

theorem firstProjection_diagonal :
    firstProjection = Matrix.diagonal firstVector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstProjection, firstVector, outerProduct, Matrix.vecMulVec_apply, Matrix.diagonal_apply]

theorem firstProjection_norm : operatorNorm firstProjection = 1 := by
  rw [operatorNorm_eq_l2, firstProjection_diagonal, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i <;> norm_num [firstVector]
  · have h := norm_le_pi_norm firstVector 0
    simpa only [firstVector, Matrix.cons_val_zero, norm_one] using h

theorem witness_norm (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    operatorNorm (witness k j) = 1 := by
  have h : operatorNorm (witness k j) ^ 2 = 1 := by
    rw [operatorNorm_eq_l2, pow_two, ← CStarRing.norm_self_mul_star]
    change operatorNorm (witness k j * (witness k j).conjTranspose) = 1
    rw [witness_reverse_gram k hk j, firstProjection_norm]
  have hn := norm_nonneg (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (witness k j))
  change 0 ≤ operatorNorm (witness k j) at hn
  nlinarith

end NLA.MI03
