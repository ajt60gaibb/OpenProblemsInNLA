/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-07.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.MI07.Definitions
import NLA.MI07.FunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import LeanCert.Tactic.IntervalAuto.PointIneq

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder Topology
open Filter Matrix
noncomputable section

namespace NLA.MI07

theorem modulus_eq_sqrt_proved {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixModulus X = CFC.sqrt (X.conjTranspose * X) ∧
    (matrixModulus X).PosSemidef := by
  exact ⟨rfl, Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg X)⟩

theorem maximalModulus_eq_of_tendsto_proved {n : ℕ}
    (X L : Matrix (Fin n) (Fin n) ℂ)
    (h : Tendsto (rootSequence X) atTop (𝓝 L)) : maximalModulus X = L := by
  exact h.limUnder_eq

open scoped Matrix.Norms.L2Operator in
theorem root_limit_iff_spectralNorm_proved {n : ℕ} (X L : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (rootSequence X) atTop (𝓝 L) ↔
    Tendsto (fun r => spectralNorm (rootSequence X r - L)) atTop (𝓝 (0 : ℝ)) := by
  exact tendsto_iff_norm_sub_tendsto_zero

theorem witnessA_hermitian : witnessA.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [witnessA, Matrix.conjTranspose_apply]

theorem directionProjector_hermitian : directionProjector.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [directionProjector, Matrix.conjTranspose_apply]

theorem witnessA_sq : witnessA ^ (2 : ℕ) = witnessA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, map_ofNat]

theorem directionProjector_sq : directionProjector ^ (2 : ℕ) = directionProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [directionProjector, pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, map_ofNat]

theorem witnessA_posSemidef : witnessA.PosSemidef := by
  simpa only [witnessA_hermitian.eq, ← pow_two, witnessA_sq] using
    Matrix.posSemidef_conjTranspose_mul_self witnessA

theorem directionProjector_posSemidef : directionProjector.PosSemidef := by
  simpa only [directionProjector_hermitian.eq, ← pow_two, directionProjector_sq] using
    Matrix.posSemidef_conjTranspose_mul_self directionProjector

theorem complement_posSemidef : (1 - witnessA).PosSemidef := by
  have h : (1 - witnessA) = Matrix.diagonal (![0, 1] : Fin 2 → ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessA, Matrix.diagonal]
  rw [h]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff]

theorem spanningSum_posDef : spanningSum.PosDef := by
  apply (witnessA_posSemidef.add directionProjector_posSemidef).posDef_iff_det_ne_zero.mpr
  norm_num [witnessA, directionProjector, Matrix.det_fin_two]

theorem modulus_of_positive_square {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : Y.PosSemidef) (h : Y * Y = X.conjTranspose * X) : matrixModulus X = Y := by
  exact CFC.sqrt_unique h hY.nonneg

theorem modulus_witnessA : matrixModulus witnessA = witnessA := by
  apply modulus_of_positive_square _ _ witnessA_posSemidef
  rw [witnessA_hermitian.eq]

theorem modulus_witnessA_adjoint : matrixModulus witnessA.conjTranspose = witnessA := by
  rw [witnessA_hermitian.eq, modulus_witnessA]

theorem modulus_witnessB : matrixModulus witnessB = (5 / 12 : ℂ) • (1 - witnessA) := by
  apply modulus_of_positive_square _ _
    (complement_posSemidef.smul (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 5 / 12))
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessB, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply, map_ofNat]

theorem modulus_witnessB_adjoint :
    matrixModulus witnessB.conjTranspose = (5 / 12 : ℂ) • witnessA := by
  apply modulus_of_positive_square _ _
    (witnessA_posSemidef.smul (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 5 / 12))
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessB, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply, map_ofNat]

theorem modulus_sum :
    matrixModulus (witnessA + witnessB) = (13 / 12 : ℂ) • directionProjector := by
  apply modulus_of_positive_square _ _
    (directionProjector_posSemidef.smul
      (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 13 / 12))
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessB, directionProjector, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, map_ofNat]

theorem modulus_sum_adjoint :
    matrixModulus (witnessA + witnessB).conjTranspose = (13 / 12 : ℂ) • witnessA := by
  apply modulus_of_positive_square _ _
    (witnessA_posSemidef.smul (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 13 / 12))
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessB, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply, map_ofNat]

theorem witness_moduli_proved :
    witnessA.PosSemidef ∧ directionProjector.PosSemidef ∧ spanningSum.PosDef ∧
    witnessA ^ (2 : ℕ) = witnessA ∧
    directionProjector ^ (2 : ℕ) = directionProjector ∧
    matrixModulus witnessA = witnessA ∧
    matrixModulus witnessA.conjTranspose = witnessA ∧
    matrixModulus witnessB = (5 / 12 : ℂ) • (1 - witnessA) ∧
    matrixModulus witnessB.conjTranspose = (5 / 12 : ℂ) • witnessA ∧
    matrixModulus (witnessA + witnessB) = (13 / 12 : ℂ) • directionProjector ∧
    matrixModulus (witnessA + witnessB).conjTranspose = (13 / 12 : ℂ) • witnessA := by
  exact ⟨witnessA_posSemidef, directionProjector_posSemidef, spanningSum_posDef,
    witnessA_sq, directionProjector_sq, modulus_witnessA, modulus_witnessA_adjoint,
    modulus_witnessB, modulus_witnessB_adjoint, modulus_sum, modulus_sum_adjoint⟩


theorem witnessA_idempotent : IsIdempotentElem witnessA := by
  simpa only [IsIdempotentElem, pow_two] using witnessA_sq

theorem directionProjector_idempotent : IsIdempotentElem directionProjector := by
  simpa only [IsIdempotentElem, pow_two] using directionProjector_sq

theorem reciprocal_tendsto_zero :
    Tendsto (fun r : ℕ => (((r + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

theorem reciprocal_pos (r : ℕ) : 0 < (((r + 1 : ℕ) : ℝ)⁻¹) := by
  exact inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos r))

theorem rootSequence_witnessA (r : ℕ) :
    rootSequence witnessA r =
      (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ)⁻¹) • witnessA := by
  rw [rootSequence, modulus_witnessA, modulus_witnessA_adjoint,
    witnessA_idempotent.pow_succ_eq r]
  rw [← two_smul ℝ witnessA,
    rpow_real_smul witnessA witnessA_posSemidef 2 _ (by norm_num) (reciprocal_pos r),
    rpow_projection witnessA witnessA_posSemidef witnessA_idempotent _ (reciprocal_pos r)]

theorem modulus_witnessB_real : matrixModulus witnessB = (5 / 12 : ℝ) • (1 - witnessA) := by
  simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using modulus_witnessB

theorem modulus_witnessB_adjoint_real :
    matrixModulus witnessB.conjTranspose = (5 / 12 : ℝ) • witnessA := by
  simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using modulus_witnessB_adjoint

theorem modulus_sum_real :
    matrixModulus (witnessA + witnessB) = (13 / 12 : ℝ) • directionProjector := by
  simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using modulus_sum

theorem modulus_sum_adjoint_real :
    matrixModulus (witnessA + witnessB).conjTranspose = (13 / 12 : ℝ) • witnessA := by
  simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using modulus_sum_adjoint

theorem rootSequence_witnessB (r : ℕ) :
    rootSequence witnessB r = (5 / 12 : ℝ) • 1 := by
  rw [rootSequence, modulus_witnessB_real, modulus_witnessB_adjoint_real,
    smul_pow, smul_pow, witnessA_idempotent.one_sub.pow_succ_eq r,
    witnessA_idempotent.pow_succ_eq r, ← smul_add, sub_add_cancel]
  rw [rpow_real_smul 1 Matrix.PosSemidef.one _ _ (by positivity) (reciprocal_pos r),
    Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 5 / 12) (Nat.succ_ne_zero r)]
  simp

theorem rootSequence_sum (r : ℕ) :
    rootSequence (witnessA + witnessB) r =
      (13 / 12 : ℝ) • CFC.rpow spanningSum (((r + 1 : ℕ) : ℝ)⁻¹) := by
  rw [rootSequence, modulus_sum_real, modulus_sum_adjoint_real,
    smul_pow, smul_pow, directionProjector_idempotent.pow_succ_eq r,
    witnessA_idempotent.pow_succ_eq r, ← smul_add, add_comm directionProjector witnessA]
  change CFC.rpow ((13 / 12 : ℝ) ^ (r + 1) • spanningSum) _ = _
  rw [rpow_real_smul spanningSum spanningSum_posDef.posSemidef _ _
      (by positivity) (reciprocal_pos r),
    Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 13 / 12) (Nat.succ_ne_zero r)]

theorem rootSequence_witnessA_tendsto : Tendsto (rootSequence witnessA) atTop (𝓝 witnessA) := by
  rw [show rootSequence witnessA = (fun r =>
    (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ)⁻¹) • witnessA) from funext rootSequence_witnessA]
  have hr := (Real.continuousAt_const_rpow (a := 2) (b := 0) (by norm_num)).tendsto.comp
    reciprocal_tendsto_zero
  simpa only [Function.comp_def, Real.rpow_zero, one_smul]
    using hr.smul_const witnessA

theorem rootSequence_witnessB_tendsto :
    Tendsto (rootSequence witnessB) atTop (𝓝 ((5 / 12 : ℂ) • 1)) := by
  rw [show rootSequence witnessB = (fun _ : ℕ => (5 / 12 : ℝ) • 1) from
    funext rootSequence_witnessB]
  simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]

theorem rootSequence_sum_tendsto :
    Tendsto (rootSequence (witnessA + witnessB)) atTop (𝓝 ((13 / 12 : ℂ) • 1)) := by
  rw [show rootSequence (witnessA + witnessB) = (fun r =>
    (13 / 12 : ℝ) • CFC.rpow spanningSum (((r + 1 : ℕ) : ℝ)⁻¹)) from funext rootSequence_sum]
  have hr := (posDef_rpow_tendsto_one spanningSum spanningSum_posDef).comp
    reciprocal_tendsto_zero
  simpa [Function.comp_def, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    using hr.const_smul (13 / 12 : ℝ)

theorem witness_root_limits_proved :
    Tendsto (rootSequence witnessA) atTop (𝓝 witnessA) ∧
    Tendsto (rootSequence witnessB) atTop (𝓝 ((5 / 12 : ℂ) • 1)) ∧
    Tendsto (rootSequence (witnessA + witnessB)) atTop (𝓝 ((13 / 12 : ℂ) • 1)) := by
  exact ⟨rootSequence_witnessA_tendsto, rootSequence_witnessB_tendsto, rootSequence_sum_tendsto⟩


theorem maximalModulus_witnessA : maximalModulus witnessA = witnessA :=
  maximalModulus_eq_of_tendsto_proved _ _ rootSequence_witnessA_tendsto

theorem maximalModulus_witnessB : maximalModulus witnessB = (5 / 12 : ℂ) • 1 :=
  maximalModulus_eq_of_tendsto_proved _ _ rootSequence_witnessB_tendsto

theorem maximalModulus_sum : maximalModulus (witnessA + witnessB) = (13 / 12 : ℂ) • 1 :=
  maximalModulus_eq_of_tendsto_proved _ _ rootSequence_sum_tendsto

theorem trace_unitaryConjugate {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) : (unitaryConjugate U H).trace = H.trace := by
  rw [unitaryConjugate, Matrix.trace_mul_cycle]
  have hu : (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
      (U : Matrix (Fin n) (Fin n) ℂ) = 1 := Matrix.UnitaryGroup.star_mul_self U
  rw [hu, one_mul]

theorem maximalModulus_sum_trace :
    (maximalModulus (witnessA + witnessB)).trace = (13 / 6 : ℂ) := by
  rw [maximalModulus_sum]
  norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

theorem orbitSum_trace (U V : Matrix.unitaryGroup (Fin 2) ℂ) :
    (unitaryConjugate U (maximalModulus witnessA) +
      unitaryConjugate V (maximalModulus witnessB)).trace = (11 / 6 : ℂ) := by
  rw [Matrix.trace_add, trace_unitaryConjugate, trace_unitaryConjugate,
    maximalModulus_witnessA, maximalModulus_witnessB]
  norm_num [witnessA, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

theorem obstruction_trace (U V : Matrix.unitaryGroup (Fin 2) ℂ) :
    (unitaryConjugate U (maximalModulus witnessA) +
      unitaryConjugate V (maximalModulus witnessB) -
      maximalModulus (witnessA + witnessB)).trace = (-1 / 3 : ℂ) := by
  rw [Matrix.trace_sub, orbitSum_trace, maximalModulus_sum_trace]
  norm_num

/-- The only interval certificate is this rational point check. Its kernel proof
is retained by the actual negative-trace contradiction below. -/
theorem scalar_gap_positive : (0 : ℝ) < 1 / 3 := by
  interval_decide (trust := kernel)

theorem no_unitary_domination (U V : Matrix.unitaryGroup (Fin 2) ℂ) :
    ¬ (maximalModulus (witnessA + witnessB) ≤
      unitaryConjugate U (maximalModulus witnessA) +
      unitaryConjugate V (maximalModulus witnessB)) := by
  intro h
  have ht := (Matrix.le_iff.mp h).trace_nonneg
  rw [obstruction_trace] at ht
  have hre := (Complex.nonneg_iff.mp ht).1
  have hr : (0 : ℝ) ≤ - (1 / 3 : ℝ) := by
    convert hre using 1
    norm_num
  exact (not_le_of_gt (neg_lt_zero.mpr scalar_gap_positive)) hr

theorem counterexample_proved :
    maximalModulus witnessA = witnessA ∧
    maximalModulus witnessB = (5 / 12 : ℂ) • 1 ∧
    maximalModulus (witnessA + witnessB) = (13 / 12 : ℂ) • 1 ∧
    (maximalModulus (witnessA + witnessB)).trace = (13 / 6 : ℂ) ∧
    ∀ U V : Matrix.unitaryGroup (Fin 2) ℂ,
      (unitaryConjugate U (maximalModulus witnessA) +
        unitaryConjugate V (maximalModulus witnessB)).trace = (11 / 6 : ℂ) ∧
      (unitaryConjugate U (maximalModulus witnessA) +
        unitaryConjugate V (maximalModulus witnessB) -
        maximalModulus (witnessA + witnessB)).trace = (-1 / 3 : ℂ) ∧
      ¬ (maximalModulus (witnessA + witnessB) ≤
        unitaryConjugate U (maximalModulus witnessA) +
        unitaryConjugate V (maximalModulus witnessB)) := by
  exact ⟨maximalModulus_witnessA, maximalModulus_witnessB, maximalModulus_sum,
    maximalModulus_sum_trace, fun U V =>
      ⟨orbitSum_trace U V, obstruction_trace U V, no_unitary_domination U V⟩⟩

theorem not_triangleConjecture_proved : ¬ TriangleConjecture := by
  intro h
  obtain ⟨U, V, hUV⟩ := h 2 (by norm_num) witnessA witnessB
  exact no_unitary_domination U V hUV

#assert_trust kernel modulus_eq_sqrt_proved
#assert_trust kernel maximalModulus_eq_of_tendsto_proved
#assert_trust kernel root_limit_iff_spectralNorm_proved
#assert_trust kernel witness_moduli_proved
#assert_trust kernel rpow_projection
#assert_trust kernel rpow_real_smul
#assert_trust kernel posDef_rpow_tendsto_one
#assert_trust kernel rootSequence_witnessA
#assert_trust kernel rootSequence_witnessB
#assert_trust kernel rootSequence_sum
#assert_trust kernel witness_root_limits_proved
#assert_trust kernel trace_unitaryConjugate
#assert_trust kernel scalar_gap_positive
#assert_trust kernel no_unitary_domination
#assert_trust kernel counterexample_proved
#assert_trust kernel not_triangleConjecture_proved

#print axioms modulus_eq_sqrt_proved
#print axioms maximalModulus_eq_of_tendsto_proved
#print axioms root_limit_iff_spectralNorm_proved
#print axioms witness_moduli_proved
#print axioms rpow_projection
#print axioms rpow_real_smul
#print axioms posDef_rpow_tendsto_one
#print axioms rootSequence_witnessA
#print axioms rootSequence_witnessB
#print axioms rootSequence_sum
#print axioms witness_root_limits_proved
#print axioms trace_unitaryConjugate
#print axioms scalar_gap_positive
#print axioms no_unitary_domination
#print axioms counterexample_proved
#print axioms not_triangleConjecture_proved

end NLA.MI07
