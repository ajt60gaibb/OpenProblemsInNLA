/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to RA-03.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.RA03.Definitions
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Classical Matrix.Norms.Frobenius
noncomputable section

namespace NLA.RA03

theorem frobeniusSq_eq_norm_sq_proved {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    frobeniusSq A = ‖A‖ ^ 2 := by
  simp only [Matrix.frobenius_norm_def, Real.rpow_two, ← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt (by positivity)]
  simp only [frobeniusSq, Complex.normSq_eq_norm_sq]

theorem frobeniusSq_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    0 ≤ frobeniusSq A := by
  rw [frobeniusSq_eq_norm_sq_proved]
  positivity

theorem frobeniusSq_eq_zero_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    frobeniusSq A = 0 ↔ A = 0 := by
  rw [frobeniusSq_eq_norm_sq_proved, sq_eq_zero_iff, norm_eq_zero]

theorem pivotMass_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (p : Pivot m n) : 0 ≤ pivotMass A p := by
  cases p with
  | none => simp only [pivotMass]; split_ifs <;> norm_num
  | some ij =>
    simp only [pivotMass]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (Complex.normSq_nonneg _) (frobeniusSq_nonneg A)

theorem pivotMass_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (∑ p : Pivot m n, pivotMass A p) = 1 := by
  rw [Fintype.sum_option]
  by_cases hA : A = 0
  · simp [pivotMass, hA]
  · simp only [pivotMass, hA, if_false, zero_add]
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_div]
    exact div_self (mt (frobeniusSq_eq_zero_iff A).mp hA)

theorem historyMass_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (k : ℕ)
    (h : Fin k → Pivot m n) : 0 ≤ historyMass A h := by
  induction k generalizing A with
  | zero => simp [historyMass]
  | succ k ih =>
    exact mul_nonneg (pivotMass_nonneg A (h 0))
      (ih (nextResidual A (h 0)) (fun i => h i.succ))

/-- Separate the first pivot from its entire remaining history, rather than
enumerating all possible histories in arbitrary dimension. -/
theorem historyMass_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (k : ℕ) :
    (∑ h : Fin k → Pivot m n, historyMass A h) = 1 := by
  induction k generalizing A with
  | zero => simp [historyMass]
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Pivot m n)).sum_comp
      (fun h => historyMass A h), Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, historyMass, Fin.cons_zero, Fin.cons_succ]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact pivotMass_sum A

theorem process_isProbability_proved {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (k : ℕ) :
    (∀ p : Pivot m n, 0 ≤ pivotMass A p) ∧
    (∑ p : Pivot m n, pivotMass A p) = 1 ∧
    (∀ h : Fin k → Pivot m n, 0 ≤ historyMass A h) ∧
    (∑ h : Fin k → Pivot m n, historyMass A h) = 1 :=
  ⟨pivotMass_nonneg A, pivotMass_sum A, historyMass_nonneg A k, historyMass_sum A k⟩

theorem expectedError_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    expectedError A 0 = frobeniusSq A := by
  simp [expectedError, historyMass, historyResidual]

/-- The finite joint law satisfies the usual conditional-expectation recurrence. -/
theorem expectedError_succ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (k : ℕ) :
    expectedError A (k + 1) =
      ∑ p : Pivot m n, pivotMass A p * expectedError (nextResidual A p) k := by
  unfold expectedError
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Pivot m n)).sum_comp
    (fun h => historyMass A h * frobeniusSq (historyResidual A h)), Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, historyMass, historyResidual, Fin.cons_zero,
    Fin.cons_succ, Finset.mul_sum, mul_assoc]

/-- On every positive-probability entry pivot, the totalized update is the
displayed cross update. `if_neg` also fixes the branch before matrix evaluation. -/
theorem pivotResidual_of_nonzero {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℂ)
    (ij : Fin m × Fin n) (h : S ij.1 ij.2 ≠ 0) :
    pivotResidual S ij =
      fun a b => S a b - S a ij.2 * S ij.1 b / S ij.1 ij.2 :=
  if_neg h

theorem witness_entry_ne_zero (i j : Fin 2) : witness i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [witness]

theorem witness_ne_zero : witness ≠ 0 := by
  intro h
  exact witness_entry_ne_zero 0 0 (congrFun (congrFun h 0) 0)

theorem witness_frobeniusSq : frobeniusSq witness = 10 := by
  norm_num [frobeniusSq, witness, Fin.sum_univ_succ]

theorem witness_gram : witness.conjTranspose * witness = witnessGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witness, witnessGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, map_ofNat]

theorem witness_pivot_mass (i j : Fin 2) :
    pivotMass witness (some (i, j)) = witnessPivotMass i j := by
  rw [pivotMass, if_neg witness_ne_zero, witness_frobeniusSq]
  fin_cases i <;> fin_cases j <;> norm_num [witness, witnessPivotMass]

theorem witness_pivot_error (i j : Fin 2) :
    frobeniusSq (pivotResidual witness (i, j)) = witnessPivotError i j := by
  rw [pivotResidual_of_nonzero witness (i, j) (witness_entry_ne_zero i j)]
  fin_cases i <;> fin_cases j <;>
    norm_num [frobeniusSq, witness, witnessPivotError, Fin.sum_univ_succ,
      Complex.normSq_div]

/-- The one-step expectation is computed from the normalized history law,
using all four jointly sampled entries and the zero-mass absorbing label. -/
theorem witness_expectedError : expectedError witness 1 = 18 / 5 := by
  rw [expectedError_succ]
  simp_rw [expectedError_zero]
  rw [Fintype.sum_option]
  have hnone : pivotMass witness none = 0 := by simp [pivotMass, witness_ne_zero]
  rw [hnone, zero_mul, zero_add, Fintype.sum_prod_type]
  simp only [nextResidual]
  simp_rw [witness_pivot_mass, witness_pivot_error]
  norm_num [witnessPivotMass, witnessPivotError, Fin.sum_univ_succ]

/-- The spectral operator defining the singular values is the actual Gram matrix. -/
theorem witness_adjoint_comp :
    (Matrix.toEuclideanLin witness).adjoint ∘ₗ Matrix.toEuclideanLin witness =
      Matrix.toEuclideanLin witnessGram := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change Matrix.toLpLin 2 2 witness.conjTranspose ∘ₗ Matrix.toLpLin 2 2 witness = _
  rw [← Matrix.toLpLin_mul_same, witness_gram]

open Polynomial in
theorem witnessGram_charpoly :
    witnessGram.charpoly = (X - C (9 : ℂ)) * (X - C (1 : ℂ)) := by
  rw [Matrix.charpoly_fin_two]
  norm_num [witnessGram, Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_succ, map_ofNat]
  ring

open Polynomial in
theorem witness_adjoint_comp_charpoly :
    ((Matrix.toEuclideanLin witness).adjoint ∘ₗ Matrix.toEuclideanLin witness).charpoly =
      (X - C (9 : ℂ)) * (X - C (1 : ℂ)) := by
  rw [witness_adjoint_comp]
  change (Matrix.toLpLin 2 2 witnessGram).charpoly = _
  rw [Matrix.toLpLin_eq_toLin, Matrix.charpoly_toLin, witnessGram_charpoly]

/-- Sorted characteristic-polynomial roots determine the actual ordered eigenvalues. -/
theorem witness_adjoint_comp_eigenvalues :
    (Matrix.toEuclideanLin witness).isSymmetric_adjoint_comp_self.eigenvalues
      (show Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) = 2 by simp) = ![(9 : ℝ), 1] := by
  have hlist := LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues
    (Matrix.toEuclideanLin witness).isSymmetric_adjoint_comp_self
    (show Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) = 2 by simp)
  rw [witness_adjoint_comp_charpoly,
    Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _)),
    Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C] at hlist
  have hsort : (({(9 : ℂ)} + {1} : Multiset ℂ).map RCLike.re).sort (· ≥ ·) =
      [(9 : ℝ), 1] := by
    norm_num [Multiset.sort_cons]
  rw [hsort] at hlist
  apply List.ofFn_inj.mp
  simpa using hlist.symm

theorem witness_singularValue_zero : singularValue witness 0 = 3 := by
  unfold singularValue
  rw [(Matrix.toEuclideanLin witness).singularValues_of_lt
    (show Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) = 2 by simp) (by norm_num),
    witness_adjoint_comp_eigenvalues]
  norm_num

theorem witness_singularValue_one : singularValue witness 1 = 1 := by
  unfold singularValue
  rw [(Matrix.toEuclideanLin witness).singularValues_of_lt
    (show Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) = 2 by simp) (by norm_num),
    witness_adjoint_comp_eigenvalues]
  norm_num

theorem witness_singularTail : singularTailSq witness 1 = 1 := by
  norm_num [singularTailSq, Finset.sum_Ico_succ_top, witness_singularValue_one]

/-- Only this rational scalar comparison needs a numerical certificate. -/
theorem strict_scalar_gap : (2 : ℝ) < 18 / 5 := by
  leancert (trust := kernel)

theorem witness_strict_violation :
    (2 : ℝ) ^ 1 * singularTailSq witness 1 < expectedError witness 1 := by
  rw [witness_singularTail, witness_expectedError]
  simpa only [pow_one, mul_one] using strict_scalar_gap

theorem counterexample_proved :
    witness ≠ 0 ∧ (∀ i j : Fin 2, witness i j ≠ 0) ∧
    frobeniusSq witness = 10 ∧
    witness.conjTranspose * witness = witnessGram ∧
    singularValue witness 0 = 3 ∧ singularValue witness 1 = 1 ∧
    (∀ i j : Fin 2, pivotMass witness (some (i, j)) = witnessPivotMass i j) ∧
    (∀ i j : Fin 2, frobeniusSq (pivotResidual witness (i, j)) = witnessPivotError i j) ∧
    expectedError witness 1 = 18 / 5 ∧ singularTailSq witness 1 = 1 ∧
    (2 : ℝ) ^ 1 * singularTailSq witness 1 < expectedError witness 1 :=
  ⟨witness_ne_zero, witness_entry_ne_zero, witness_frobeniusSq, witness_gram,
    witness_singularValue_zero, witness_singularValue_one, witness_pivot_mass,
    witness_pivot_error, witness_expectedError, witness_singularTail, witness_strict_violation⟩

/-- All dimension and rank conditions of the original assertion hold at this witness. -/
theorem not_squaredErrorConjecture_proved : ¬ SquaredErrorConjecture := by
  intro h
  have hbound := h 2 2 (by norm_num) (by norm_num) witness 1 (by norm_num) (by norm_num)
  exact (not_le_of_gt witness_strict_violation) hbound

#assert_trust kernel frobeniusSq_eq_norm_sq_proved
#print axioms frobeniusSq_eq_norm_sq_proved
#assert_trust kernel process_isProbability_proved
#print axioms process_isProbability_proved
#assert_trust kernel witness_singularValue_zero
#print axioms witness_singularValue_zero
#assert_trust kernel witness_singularValue_one
#print axioms witness_singularValue_one
#assert_trust kernel witness_expectedError
#print axioms witness_expectedError
#assert_trust kernel strict_scalar_gap
#print axioms strict_scalar_gap
#assert_trust kernel counterexample_proved
#print axioms counterexample_proved
#assert_trust kernel not_squaredErrorConjecture_proved
#print axioms not_squaredErrorConjecture_proved

end NLA.RA03
