/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to IE-18.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.IE18.Definitions
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators NNReal Classical
noncomputable section

namespace NLA.IE18

theorem witnessInitial_ne_zero : witnessInitial ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [witnessInitial] at h0

theorem witnessFirst_ne_zero : witnessFirst ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [witnessFirst] at h0

/-- Both denominators are obtained from the actual matrix-vector products. -/
theorem first_denominator :
    squaredNorm ((1 - witnessMatrix).mulVec witnessInitial) = 61 / 50 := by
  norm_num [squaredNorm, Matrix.sub_mulVec, Matrix.one_mulVec,
    witnessMatrix, Matrix.mulVec_diagonal, witnessEigenvalues, witnessInitial,
    Fin.sum_univ_succ]

theorem first_coefficient :
    residualCoefficient witnessMatrix witnessInitial = 90 / 61 := by
  rw [residualCoefficient, first_denominator]
  norm_num [dotProduct, Matrix.sub_mulVec, Matrix.one_mulVec,
    witnessMatrix, Matrix.mulVec_diagonal, witnessEigenvalues, witnessInitial,
    Fin.sum_univ_succ]

theorem first_residual :
    residualMap witnessMatrix witnessInitial = witnessFirst := by
  rw [residualMap, if_neg witnessInitial_ne_zero, first_coefficient]
  ext i
  fin_cases i <;>
    norm_num [Matrix.sub_mulVec, Matrix.one_mulVec, witnessMatrix,
      Matrix.mulVec_diagonal, witnessEigenvalues, witnessInitial, witnessFirst]
      <;> norm_num [Matrix.vecHead, Matrix.vecTail, Matrix.mulVec_diagonal,
        Matrix.cons_val_two]

theorem second_denominator :
    squaredNorm ((1 - witnessMatrix).mulVec witnessFirst) = 1381 / 93025 := by
  norm_num [squaredNorm, Matrix.sub_mulVec, Matrix.one_mulVec,
    witnessMatrix, Matrix.mulVec_diagonal, witnessEigenvalues, witnessFirst,
    Fin.sum_univ_succ]

theorem second_coefficient :
    residualCoefficient witnessMatrix witnessFirst = 3140 / 1381 := by
  rw [residualCoefficient, second_denominator]
  norm_num [dotProduct, Matrix.sub_mulVec, Matrix.one_mulVec,
    witnessMatrix, Matrix.mulVec_diagonal, witnessEigenvalues, witnessFirst,
    Fin.sum_univ_succ]

theorem second_residual :
    residualMap witnessMatrix witnessFirst = witnessSecond := by
  rw [residualMap, if_neg witnessFirst_ne_zero, second_coefficient]
  ext i
  fin_cases i <;>
    norm_num [Matrix.sub_mulVec, Matrix.one_mulVec, witnessMatrix,
      Matrix.mulVec_diagonal, witnessEigenvalues, witnessFirst, witnessSecond]
      <;> norm_num [Matrix.vecHead, Matrix.vecTail, Matrix.mulVec_diagonal,
        Matrix.cons_val_two]

theorem four_step_residual :
    fourStepResidual witnessMatrix witnessInitial = witnessSecond := by
  rw [fourStepResidual, first_residual, second_residual]

theorem initial_squaredNorm : squaredNorm witnessInitial = 3 := by
  norm_num [squaredNorm, witnessInitial, Fin.sum_univ_succ]

theorem second_squaredNorm : squaredNorm witnessSecond = 1920682 / 7096546081 := by
  norm_num [squaredNorm, witnessSecond, Fin.sum_univ_succ]

theorem squared_amplification :
    squaredNorm (fourStepResidual witnessMatrix witnessInitial) /
      squaredNorm witnessInitial = 1920682 / 21289638243 := by
  rw [four_step_residual, second_squaredNorm, initial_squaredNorm]
  norm_num

theorem residual_certificate_proved :
    witnessInitial ≠ 0 ∧
    squaredNorm ((1 - witnessMatrix).mulVec witnessInitial) = 61 / 50 ∧
    residualCoefficient witnessMatrix witnessInitial = 90 / 61 ∧
    residualMap witnessMatrix witnessInitial = witnessFirst ∧
    witnessFirst ≠ 0 ∧
    squaredNorm ((1 - witnessMatrix).mulVec witnessFirst) = 1381 / 93025 ∧
    residualCoefficient witnessMatrix witnessFirst = 3140 / 1381 ∧
    fourStepResidual witnessMatrix witnessInitial = witnessSecond ∧
    squaredNorm (fourStepResidual witnessMatrix witnessInitial) /
      squaredNorm witnessInitial = 1920682 / 21289638243 :=
  ⟨witnessInitial_ne_zero, first_denominator, first_coefficient, first_residual,
    witnessFirst_ne_zero, second_denominator, second_coefficient, four_step_residual,
    squared_amplification⟩

theorem witness_posDef : witnessMatrix.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [witnessEigenvalues]

theorem complement_diagonal :
    1 - witnessMatrix = Matrix.diagonal (![9 / 10, 1 / 2, 2 / 5] : Fin 3 → ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessMatrix, witnessEigenvalues, Matrix.diagonal_apply, Matrix.one_apply]

theorem complement_posDef : (1 - witnessMatrix).PosDef := by
  rw [complement_diagonal]
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num

theorem witness_ne_zero : witnessMatrix ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [witnessMatrix, witnessEigenvalues, Matrix.diagonal_apply] at h00

theorem witness_spectrum :
    spectrum ℝ witnessMatrix = Set.range witnessEigenvalues := by
  exact spectrum_diagonal witnessEigenvalues

theorem one_not_mem_spectrum : (1 : ℝ) ∉ spectrum ℝ witnessMatrix := by
  rw [witness_spectrum]
  rintro ⟨i, hi⟩
  fin_cases i <;> norm_num [witnessEigenvalues] at hi

/-- Each pair of the explicit diagonal values satisfies the proposed bound. -/
theorem explicit_pair_bound (i j : Fin 3) :
    ‖pairQuotient (witnessEigenvalues i) (witnessEigenvalues j)‖₊ ^ 2 ≤
      (1 / 121 : ℝ≥0) := by
  rw [← NNReal.coe_le_coe]
  fin_cases i <;> fin_cases j <;>
    norm_num [pairQuotient, witnessEigenvalues, Real.norm_eq_abs]

/-- Membership in the true spectrum constrains every actual chosen eigenvalue. -/
theorem eigenvalue_in_witness_range (hM : witnessMatrix.IsHermitian) (i : Fin 3) :
    ∃ k : Fin 3, witnessEigenvalues k = hM.eigenvalues i := by
  have hi := hM.eigenvalues_mem_spectrum_real i
  rw [witness_spectrum] at hi
  exact hi

/-- The maximum uses the actual eigenvalue list; its order is never evaluated. -/
theorem actual_pairMaximum (hM : witnessMatrix.IsHermitian) :
    pairMaximum hM = 1 / 121 := by
  let pairs := (Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun ij => ij.1 ≠ ij.2)
  let f := fun ij : Fin 3 × Fin 3 =>
    ‖pairQuotient (hM.eigenvalues ij.1) (hM.eigenvalues ij.2)‖₊ ^ 2
  have hu : pairs.sup f ≤ (1 / 121 : ℝ≥0) := by
    apply Finset.sup_le
    intro ij _
    obtain ⟨i, hi⟩ := eigenvalue_in_witness_range hM ij.1
    obtain ⟨j, hj⟩ := eigenvalue_in_witness_range hM ij.2
    dsimp [f]
    rw [← hi, ← hj]
    exact explicit_pair_bound i j
  have hi_mem : (1 / 10 : ℝ) ∈ spectrum ℝ witnessMatrix := by
    rw [witness_spectrum]
    exact ⟨0, rfl⟩
  have hj_mem : (3 / 5 : ℝ) ∈ spectrum ℝ witnessMatrix := by
    rw [witness_spectrum]
    exact ⟨2, rfl⟩
  rw [hM.spectrum_real_eq_range_eigenvalues] at hi_mem hj_mem
  obtain ⟨i, hi⟩ := hi_mem
  obtain ⟨j, hj⟩ := hj_mem
  have hij : i ≠ j := by
    intro heq
    rw [heq, hj] at hi
    norm_num at hi
  have hmem : (i, j) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
  have hterm : f (i, j) = (1 / 121 : ℝ≥0) := by
    apply NNReal.coe_injective
    norm_num [f, hi, hj, pairQuotient, Real.norm_eq_abs]
  have hl : (1 / 121 : ℝ≥0) ≤ pairs.sup f := by
    rw [← hterm]
    exact Finset.le_sup hmem
  have heq := le_antisymm hu hl
  change (↑(pairs.sup f) : ℝ) = 1 / 121
  rw [heq]
  norm_num

theorem squaredNorm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ squaredNorm v := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (v i))

theorem euclideanNorm_sq {n : ℕ} (v : Fin n → ℝ) :
    euclideanNorm v ^ 2 = squaredNorm v :=
  Real.sq_sqrt (squaredNorm_nonneg v)

theorem actual_amplification_sq :
    amplification witnessMatrix witnessInitial ^ 2 = 1920682 / 21289638243 := by
  rw [amplification, div_pow, euclideanNorm_sq, euclideanNorm_sq]
  exact squared_amplification

/-- A single rational point certificate; the eigenvalue factor must be squared again. -/
theorem strict_scalar_gap : (1 : ℝ) / 14641 < 1920682 / 21289638243 := by
  leancert (trust := kernel)

/-- Nonnegative Euclidean norms justify passing from the squared gap to the target. -/
theorem strict_amplification_gap :
    (1 : ℝ) / 121 < amplification witnessMatrix witnessInitial := by
  have hn : 0 ≤ amplification witnessMatrix witnessInitial := by
    exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 121) hn).mp
  rw [actual_amplification_sq]
  have hs : ((1 : ℝ) / 121) ^ 2 = 1 / 14641 := by norm_num
  rw [hs]
  exact strict_scalar_gap

theorem actual_gap (hM : witnessMatrix.IsHermitian) :
    pairMaximum hM < amplification witnessMatrix witnessInitial := by
  rw [actual_pairMaximum]
  exact strict_amplification_gap

theorem not_isGreatest (hM : witnessMatrix.IsHermitian) :
    ¬ IsGreatest (amplificationSet witnessMatrix) (pairMaximum hM) := by
  intro hg
  have hmem : amplification witnessMatrix witnessInitial ∈ amplificationSet witnessMatrix :=
    ⟨witnessInitial, witnessInitial_ne_zero, rfl⟩
  exact (not_le_of_gt (actual_gap hM)) (hg.2 hmem)

theorem counterexample_proved :
    ∃ hM : witnessMatrix.IsHermitian,
      witnessMatrix ≠ 0 ∧
      (1 : ℝ) ∉ spectrum ℝ witnessMatrix ∧
      witnessMatrix.PosDef ∧ (1 - witnessMatrix).PosDef ∧
      spectrum ℝ witnessMatrix = Set.range witnessEigenvalues ∧
      witnessInitial ≠ 0 ∧
      pairMaximum hM = 1 / 121 ∧
      pairMaximum hM < amplification witnessMatrix witnessInitial ∧
      ¬ IsGreatest (amplificationSet witnessMatrix) (pairMaximum hM) := by
  let hM := witness_posDef.isHermitian
  exact ⟨hM, witness_ne_zero, one_not_mem_spectrum, witness_posDef, complement_posDef,
    witness_spectrum, witnessInitial_ne_zero, actual_pairMaximum hM, actual_gap hM,
    not_isGreatest hM⟩

theorem not_fourStepConjecture_proved : ¬ FourStepConjecture := by
  intro h
  let hM := witness_posDef.isHermitian
  exact not_isGreatest hM (h 3 (by norm_num) witnessMatrix witness_ne_zero hM
    one_not_mem_spectrum)

#assert_trust kernel strict_scalar_gap
#print axioms strict_scalar_gap
#assert_trust kernel residual_certificate_proved
#print axioms residual_certificate_proved
#assert_trust kernel actual_pairMaximum
#print axioms actual_pairMaximum
#assert_trust kernel counterexample_proved
#print axioms counterexample_proved
#assert_trust kernel not_fourStepConjecture_proved
#print axioms not_fourStepConjecture_proved

end NLA.IE18
