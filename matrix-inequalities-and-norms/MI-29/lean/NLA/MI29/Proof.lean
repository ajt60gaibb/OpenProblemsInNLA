/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-29.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.MI29.Definitions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import LeanCert.Tactic.IntervalAuto.PointIneq

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section

namespace NLA.MI29

theorem spectralPower_natCast_proved {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (r : ℕ) : spectralPower A (r : ℝ) = A ^ r := by
  exact CFC.rpow_natCast A r hA.nonneg

theorem modulus_power_eight_proved {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixModulus X = CFC.sqrt (X.conjTranspose * X) ∧
    (matrixModulus X).PosSemidef ∧
    spectralPower (matrixModulus X) 8 = (X.conjTranspose * X) ^ (4 : ℕ) := by
  have hpos : (matrixModulus X).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg X)
  refine ⟨rfl, hpos, ?_⟩
  change spectralPower (matrixModulus X) ((8 : ℕ) : ℝ) = _
  rw [spectralPower_natCast_proved _ hpos 8]
  have hs : matrixModulus X ^ (2 : ℕ) = X.conjTranspose * X := CFC.abs_sq X
  calc
    matrixModulus X ^ (8 : ℕ) = (matrixModulus X ^ (2 : ℕ)) ^ (4 : ℕ) := by
      rw [← pow_mul]
    _ = (X.conjTranspose * X) ^ (4 : ℕ) := by rw [hs]

theorem spectralPower_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (r : ℝ) : (spectralPower A r).PosDef := by
  exact Matrix.isStrictlyPositive_iff_posDef.mp (IsStrictlyPositive.rpow A r hA.isStrictlyPositive)

theorem spectralPower_posSemidef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) : (spectralPower A r).PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg

theorem comparison_positive_real_proved {n : ℕ} (_hn : 1 ≤ n)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (_hB : B.IsHermitian) (_hBinv : IsUnit B)
    (k p : ℝ) (_hk : 0 ≤ k) (_hp : 0 ≤ p) :
    (leftDet A B k p).im = 0 ∧ 0 < (leftDet A B k p).re ∧
    (rightDet A B k p).im = 0 ∧ 0 < (rightDet A B k p).re := by
  have hL : (leftMatrix A B k p).PosDef :=
    (spectralPower_posDef A hA k).add_posSemidef
      (spectralPower_posSemidef (matrixModulus (A * B)) p)
  have hR : (rightMatrix A B k p).PosDef :=
    (spectralPower_posDef A hA k).add_posSemidef
      (spectralPower_posSemidef (matrixModulus (B * A)) p)
  have hld := Complex.pos_iff.mp hL.det_pos
  have hrd := Complex.pos_iff.mp hR.det_pos
  exact ⟨hld.2.symm, hld.1, hrd.2.symm, hrd.1⟩

theorem witnessA_posDef : witnessA.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.pos_iff]

theorem witnessB_hermitian : witnessB.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessB, witnessM, Matrix.conjTranspose_apply, map_ofNat]

theorem witnessB_det : witnessB.det = (-1 / 125 : ℂ) := by
  norm_num [witnessB, witnessM, Matrix.det_fin_three,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem witnessB_isUnit : IsUnit witnessB := by
  rw [Matrix.isUnit_iff_isUnit_det, witnessB_det]
  norm_num

theorem witnessB_not_posSemidef : ¬ witnessB.PosSemidef := by
  intro h
  have hd : 0 ≤ witnessB (0 : Fin 3) 0 := h.diag_nonneg
  have hr : (0 : ℝ) ≤ (witnessB 0 0).re := (Complex.nonneg_iff.mp hd).1
  norm_num [witnessB, witnessM] at hr

theorem neg_witnessB_not_posSemidef : ¬ (-witnessB).PosSemidef := by
  intro h
  have hd : 0 ≤ (-witnessB) (1 : Fin 3) 1 := h.diag_nonneg
  have hr : (0 : ℝ) ≤ ((-witnessB) 1 1).re := (Complex.nonneg_iff.mp hd).1
  norm_num [witnessB, witnessM] at hr

theorem gram_AB {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).conjTranspose * (A * B) = B * A ^ (2 : ℕ) * B := by
  simp only [Matrix.conjTranspose_mul, hA.eq, hB.eq, pow_two, Matrix.mul_assoc]

theorem gram_BA {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (B * A).conjTranspose * (B * A) = A * B ^ (2 : ℕ) * A := by
  exact gram_AB B A hB hA

theorem witnessA_spectral_six : spectralPower witnessA 6 = witnessA ^ (6 : ℕ) := by
  exact spectralPower_natCast_proved witnessA witnessA_posDef.posSemidef 6

theorem witness_AB_spectral_eight :
    spectralPower (matrixModulus (witnessA * witnessB)) 8 =
      (witnessB * witnessA ^ (2 : ℕ) * witnessB) ^ (4 : ℕ) := by
  rw [(modulus_power_eight_proved (witnessA * witnessB)).2.2,
    gram_AB witnessA witnessB witnessA_posDef.isHermitian witnessB_hermitian]

theorem witness_BA_spectral_eight :
    spectralPower (matrixModulus (witnessB * witnessA)) 8 =
      (witnessA * witnessB ^ (2 : ℕ) * witnessA) ^ (4 : ℕ) := by
  rw [(modulus_power_eight_proved (witnessB * witnessA)).2.2,
    gram_BA witnessA witnessB witnessA_posDef.isHermitian witnessB_hermitian]

/- The following finite matrices are proof certificates only. Each is verified
   against the actual matrix operations; none is assumed as a hypothesis. -/
private def diagSix : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![64, 1, 1 / 64]

private def gramLeft : Matrix (Fin 3) (Fin 3) ℂ :=
  !![8 / 25, -6 / 25, 4 / 25;
     -6 / 25, 18 / 25, 1 / 10;
     4 / 25, 1 / 10, 17 / 100]

private def gramRight : Matrix (Fin 3) (Fin 3) ℂ :=
  !![4 / 5, 0, 4 / 25;
     0, 9 / 25, 2 / 25;
     4 / 25, 2 / 25, 1 / 20]

private def gramLeftSquared : Matrix (Fin 3) (Fin 3) ℂ :=
  !![116 / 625, -146 / 625, 34 / 625;
     -146 / 625, 293 / 500, 253 / 5000;
     34 / 625, 253 / 5000, 129 / 2000]

private def gramRightSquared : Matrix (Fin 3) (Fin 3) ℂ :=
  !![416 / 625, 8 / 625, 17 / 125;
     8 / 625, 17 / 125, 41 / 1250;
     17 / 125, 41 / 1250, 69 / 2000]

private def leftCertificate : Matrix (Fin 3) (Fin 3) ℂ :=
  !![25035928 / 390625, -277333 / 1562500, 5579 / 3125000;
     -277333 / 1562500, 35013133 / 25000000, 1010373 / 50000000;
     5579 / 3125000, 1010373 / 50000000, 2530497 / 100000000]

private def rightCertificate : Matrix (Fin 3) (Fin 3) ℂ :=
  !![5036069 / 78125, 11501 / 781250, 597709 / 6250000;
     11501 / 781250, 1593337 / 1562500, 18333 / 2500000;
     597709 / 6250000, 18333 / 2500000, 3638709 / 100000000]

private theorem witnessA_six_eq : witnessA ^ (6 : ℕ) = diagSix := by
  rw [witnessA, Matrix.diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> norm_num [diagSix]

private theorem gramLeft_eq : witnessB * witnessA ^ (2 : ℕ) * witnessB = gramLeft := by
  rw [witnessA, Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessB, witnessM, gramLeft, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.diagonal, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;>
    norm_num [Fin.ext_iff]

private theorem gramRight_eq : witnessA * witnessB ^ (2 : ℕ) * witnessA = gramRight := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessB, witnessM, gramRight, pow_two, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.diagonal, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem gramLeft_sq : gramLeft ^ (2 : ℕ) = gramLeftSquared := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramLeft, gramLeftSquared, pow_two, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem gramRight_sq : gramRight ^ (2 : ℕ) = gramRightSquared := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramRight, gramRightSquared, pow_two, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem fourth_as_square (X : Matrix (Fin 3) (Fin 3) ℂ) :
    X ^ (4 : ℕ) = X ^ (2 : ℕ) * X ^ (2 : ℕ) := by
  rw [← pow_add]

private theorem leftCertificate_eq : leftMatrix witnessA witnessB 6 8 = leftCertificate := by
  rw [leftMatrix, witnessA_spectral_six, witness_AB_spectral_eight,
    witnessA_six_eq, gramLeft_eq, fourth_as_square, gramLeft_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [diagSix, gramLeftSquared, leftCertificate, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.diagonal, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem rightCertificate_eq : rightMatrix witnessA witnessB 6 8 = rightCertificate := by
  rw [rightMatrix, witnessA_spectral_six, witness_BA_spectral_eight,
    witnessA_six_eq, gramRight_eq, fourth_as_square, gramRight_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [diagSix, gramRightSquared, rightCertificate, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.diagonal, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem leftDet_exact : leftDet witnessA witnessB 6 8 =
    (136990346414301954149 / 61035156250000000000 : ℂ) := by
  rw [leftDet, leftCertificate_eq]
  norm_num [leftCertificate, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]

theorem rightDet_exact : rightDet witnessA witnessB 6 8 =
    (4537743716162890657 / 1907348632812500000 : ℂ) := by
  rw [rightDet, rightCertificate_eq]
  norm_num [rightCertificate, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]

theorem determinant_gap_exact :
    rightDet witnessA witnessB 6 8 - leftDet witnessA witnessB 6 8 =
      (21036678407451 / 156250000000000 : ℂ) := by
  rw [leftDet_exact, rightDet_exact]
  norm_num

theorem scalar_gap_positive : (0 : ℝ) < 21036678407451 / 156250000000000 := by
  interval_decide (trust := kernel)

theorem witness_strict_violation :
    leftDet witnessA witnessB 6 8 < rightDet witnessA witnessB 6 8 := by
  apply sub_pos.mp
  rw [determinant_gap_exact]
  apply Complex.pos_iff.mpr
  constructor
  · convert scalar_gap_positive using 1
    norm_num
  · norm_num

theorem counterexample_proved :
    witnessA.PosDef ∧ witnessB.IsHermitian ∧ IsUnit witnessB ∧
    witnessB.det = (-1 / 125 : ℂ) ∧
    ¬ witnessB.PosSemidef ∧ ¬ (-witnessB).PosSemidef ∧
    spectralPower witnessA 6 = witnessA ^ (6 : ℕ) ∧
    spectralPower (matrixModulus (witnessA * witnessB)) 8 =
      (witnessB * witnessA ^ (2 : ℕ) * witnessB) ^ (4 : ℕ) ∧
    spectralPower (matrixModulus (witnessB * witnessA)) 8 =
      (witnessA * witnessB ^ (2 : ℕ) * witnessA) ^ (4 : ℕ) ∧
    leftDet witnessA witnessB 6 8 =
      (136990346414301954149 / 61035156250000000000 : ℂ) ∧
    rightDet witnessA witnessB 6 8 =
      (4537743716162890657 / 1907348632812500000 : ℂ) ∧
    rightDet witnessA witnessB 6 8 - leftDet witnessA witnessB 6 8 =
      (21036678407451 / 156250000000000 : ℂ) ∧
    leftDet witnessA witnessB 6 8 < rightDet witnessA witnessB 6 8 := by
  exact ⟨witnessA_posDef, witnessB_hermitian, witnessB_isUnit, witnessB_det,
    witnessB_not_posSemidef, neg_witnessB_not_posSemidef, witnessA_spectral_six,
    witness_AB_spectral_eight, witness_BA_spectral_eight, leftDet_exact, rightDet_exact,
    determinant_gap_exact, witness_strict_violation⟩

theorem not_modulusDeterminantConjecture_proved : ¬ ModulusDeterminantConjecture := by
  intro h
  have hle := h 3 (by norm_num) witnessA witnessB witnessA_posDef witnessB_hermitian
    witnessB_isUnit 6 8 (by norm_num) (by norm_num)
  exact (not_le_of_gt witness_strict_violation) hle

#assert_trust kernel spectralPower_natCast_proved
#assert_trust kernel modulus_power_eight_proved
#assert_trust kernel comparison_positive_real_proved
#assert_trust kernel scalar_gap_positive
#assert_trust kernel leftDet_exact
#assert_trust kernel rightDet_exact
#assert_trust kernel determinant_gap_exact
#assert_trust kernel witness_strict_violation
#assert_trust kernel counterexample_proved
#assert_trust kernel not_modulusDeterminantConjecture_proved

#print axioms spectralPower_natCast_proved
#print axioms modulus_power_eight_proved
#print axioms comparison_positive_real_proved
#print axioms scalar_gap_positive
#print axioms leftDet_exact
#print axioms rightDet_exact
#print axioms determinant_gap_exact
#print axioms witness_strict_violation
#print axioms counterexample_proved
#print axioms not_modulusDeterminantConjecture_proved

end NLA.MI29
