/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to IE-19.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.IE19.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped NNReal
noncomputable section

namespace NLA.IE19

/-- The matrix satisfies the original entrywise bounds and weak dominance. -/
theorem witness_admissible : Admissible 1 1 witness := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [witness, Matrix.transpose_apply]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [witness, comparisonMatrix, Fin.ext_iff]
  · intro i
    have hsum : (∑ j : Fin 3, witness i j) = 3 := by
      fin_cases i <;> norm_num [witness, Fin.sum_univ_succ]
    have hdiag : witness i i = 2 := by
      fin_cases i <;> norm_num [witness]
    have herase := Finset.sum_erase_add Finset.univ (fun j : Fin 3 => witness i j)
      (Finset.mem_univ i)
    linarith

/-- Exact matrix multiplication checks the candidate inverse. -/
theorem witness_mul_candidate : witness * witnessInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witness, witnessInverse, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

theorem witness_det_isUnit : IsUnit witness.det :=
  Matrix.isUnit_det_of_right_inverse witness_mul_candidate

theorem witness_inverse_eq : witness⁻¹ = witnessInverse :=
  Matrix.inv_eq_right_inv witness_mul_candidate

/-- Expand the comparison matrix before taking finite matrix products. -/
theorem comparison_matrix_explicit : comparisonMatrix (n := 3) 1 1 =
    !![(2 : ℝ), 1, 1; 1, 2, 1; 1, 1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [comparisonMatrix]

/-- The comparison matrix is also genuinely invertible. -/
theorem comparison_mul_candidate :
    comparisonMatrix (n := 3) 1 1 * comparisonInverse = 1 := by
  rw [comparison_matrix_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comparisonInverse, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem comparison_det_isUnit : IsUnit (comparisonMatrix (n := 3) 1 1).det :=
  Matrix.isUnit_det_of_right_inverse comparison_mul_candidate

theorem comparison_inverse_eq :
    (comparisonMatrix (n := 3) 1 1)⁻¹ = comparisonInverse :=
  Matrix.inv_eq_right_inv comparison_mul_candidate

/-- Every row has the claimed sum; the finite maximum is therefore exact. -/
theorem witness_inverse_rowSumNorm : rowSumNorm witness⁻¹ = 7 / 9 := by
  rw [witness_inverse_eq]
  have hrow : ∀ i : Fin 3, (∑ j : Fin 3, ‖witnessInverse i j‖₊) = (7 / 9 : ℝ≥0) := by
    intro i
    apply NNReal.coe_injective
    fin_cases i <;> norm_num [witnessInverse, Fin.sum_univ_succ, Real.norm_eq_abs]
  simp only [rowSumNorm, hrow]
  rw [Finset.sup_const Finset.univ_nonempty]
  norm_num

theorem comparison_inverse_rowSumNorm :
    rowSumNorm (comparisonMatrix (n := 3) 1 1)⁻¹ = 5 / 4 := by
  rw [comparison_inverse_eq]
  have hrow : ∀ i : Fin 3, (∑ j : Fin 3, ‖comparisonInverse i j‖₊) = (5 / 4 : ℝ≥0) := by
    intro i
    apply NNReal.coe_injective
    fin_cases i <;> norm_num [comparisonInverse, Fin.sum_univ_succ, Real.norm_eq_abs]
  simp only [rowSumNorm, hrow]
  rw [Finset.sup_const Finset.univ_nonempty]
  norm_num

/-- The only numerical inequality is a kernel-checked rational point certificate. -/
theorem strict_scalar_gap : (7 : ℝ) / 9 < 5 / 4 := by
  leancert (trust := kernel)

/-- The exact admissible counterexample uses actual matrix inverses. -/
theorem counterexample_proved :
    Admissible 1 1 witness ∧
    IsUnit witness.det ∧
    IsUnit (comparisonMatrix (n := 3) 1 1).det ∧
    rowSumNorm witness⁻¹ = 7 / 9 ∧
    rowSumNorm (comparisonMatrix (n := 3) 1 1)⁻¹ = 5 / 4 ∧
    rowSumNorm witness⁻¹ < comparisonBound 3 1 1 := by
  refine ⟨witness_admissible, witness_det_isUnit, comparison_det_isUnit,
    witness_inverse_rowSumNorm, comparison_inverse_rowSumNorm, ?_⟩
  have hcomparison : comparisonBound 3 1 1 = (5 : ℝ) / 4 := by
    norm_num [comparisonBound]
  rw [witness_inverse_rowSumNorm, hcomparison]
  exact strict_scalar_gap

/-- One admissible order-three matrix refutes the original universal inequality. -/
theorem not_lowerBoundConjecture_proved : ¬ LowerBoundConjecture := by
  intro h
  have hbound := h 3 (by norm_num) 1 1 (by norm_num) (by norm_num) witness
    witness_admissible
  exact (not_le_of_gt counterexample_proved.2.2.2.2.2) hbound

/-- The failed inequality also refutes its equality-characterized sharpening. -/
theorem not_sharpConjecture_proved : ¬ SharpConjecture := by
  intro h
  apply not_lowerBoundConjecture_proved
  intro n hn α m hm hα J hJ
  exact (h n hn α m hm hα J hJ).1

#assert_trust kernel strict_scalar_gap
#print axioms strict_scalar_gap
#assert_trust kernel counterexample_proved
#print axioms counterexample_proved
#assert_trust kernel not_lowerBoundConjecture_proved
#print axioms not_lowerBoundConjecture_proved
#assert_trust kernel not_sharpConjecture_proved
#print axioms not_sharpConjecture_proved

end NLA.IE19
