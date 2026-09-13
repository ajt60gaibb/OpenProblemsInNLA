/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: George Stepaniants

Actual CFC modulus and contraction bounds for Matthew J. Colbrook's MI-03
argument. Department of Computing and Mathematical Sciences, California
Institute of Technology, Pasadena, California, USA. AI-assisted formalization.
-/
import NLA.MI03.Definitions
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI03

theorem matrixModulus_eq_abs {n : ℕ} (A : Mat n) : matrixModulus A = CFC.abs A := rfl

theorem operatorNorm_eq_l2 {n : ℕ} (A : Mat n) : operatorNorm A = ‖A‖ :=
  Matrix.l2_opNorm_toEuclideanCLM A

theorem modulus_nonneg {n : ℕ} (A : Mat n) : (matrixModulus A).PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg A)

theorem modulus_square {n : ℕ} (A : Mat n) :
    matrixModulus A * matrixModulus A = A.conjTranspose * A := by
  exact CFC.abs_mul_abs A

theorem modulus_norm {n : ℕ} (A : Mat n) :
    operatorNorm (matrixModulus A) = operatorNorm A := by
  simp only [operatorNorm_eq_l2, matrixModulus_eq_abs, CFC.norm_abs]

theorem modulus_semantics_proved {n : ℕ} (_hn : 1 ≤ n) (A : Mat n) :
    (matrixModulus A).PosSemidef ∧
    matrixModulus A * matrixModulus A = A.conjTranspose * A ∧
    operatorNorm (matrixModulus A) = operatorNorm A :=
  ⟨modulus_nonneg A, modulus_square A, modulus_norm A⟩

theorem contraction_modulus_proved {n : ℕ} (_hn : 1 ≤ n) (A : Mat n)
    (hA : operatorNorm A ≤ 1) :
    ((1 : Mat n) - matrixModulus A).PosSemidef ∧
    (matrixModulus A - matrixModulus A * matrixModulus A).PosSemidef := by
  have hr : 0 ≤ matrixModulus A := (modulus_nonneg A).nonneg
  have hb : matrixModulus A ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (matrixModulus A) hr).mp (by
      rw [← operatorNorm_eq_l2, modulus_norm]
      exact hA)
  have hd : 0 ≤ (1 : Mat n) - matrixModulus A := sub_nonneg.mpr hb
  refine ⟨Matrix.nonneg_iff_posSemidef.mp hd, ?_⟩
  have hc : Commute (matrixModulus A) (1 - matrixModulus A) :=
    (Commute.one_right _).sub_right (Commute.refl _)
  have hp := hc.mul_nonneg hr hd
  simpa only [mul_sub, mul_one] using Matrix.nonneg_iff_posSemidef.mp hp

end NLA.MI03
