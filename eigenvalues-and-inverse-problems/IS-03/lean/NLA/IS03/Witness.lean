/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Actual characteristic polynomial of Colbrook's unchanged sparse witness.
The largest determinant expanded is of order four.
-/
import NLA.IS03.Algebra

noncomputable section
open Matrix Polynomial
open scoped Matrix
namespace NLA.IS03

private def firstBlock : RealMatrix 3 := !![1/2, 0, 0; 0, 0, 1; 0, 1, 0]
private def cycleFour : RealMatrix 4 := !![0, 1, 0, 0; 0, 0, 1, 0;
  0, 0, 0, 1; 1, 0, 0, 0]

private theorem firstBlock_charpoly : firstBlock.charpoly = (X - C (1/2)) * (X^2-1) := by
  simp [Matrix.charpoly, Matrix.det_fin_three, firstBlock]
  ring

private theorem cycleFour_charpoly : cycleFour.charpoly = X^4-1 := by
  have hc : cycleFour.charmatrix = !![X, -1, 0, 0; 0, X, -1, 0;
      0, 0, X, -1; -1, 0, 0, X] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [cycleFour, Matrix.charmatrix_apply]
  rw [Matrix.charpoly, hc, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove,
    Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceSucc, Fin.reduceCastSucc,
    Fin.ext_iff]
  ring

theorem witness_charpoly : witnessMatrix.charpoly = witnessPolynomial := by
  let e : Fin 7 ≃ Fin 3 ⊕ Fin 4 := (finSumFinEquiv (m := 3) (n := 4)).symm
  have hb : Matrix.reindex e e witnessMatrix = Matrix.fromBlocks firstBlock 0 0 cycleFour := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> rfl
  have hc := Matrix.charpoly_reindex e witnessMatrix
  rw [hb, Matrix.charpoly_fromBlocks_zero₁₂, firstBlock_charpoly, cycleFour_charpoly] at hc
  exact hc.symm

theorem witness_normalizedDerivative :
    normalizedDerivative 7 witnessPolynomial = derivativePolynomial := by
  apply Polynomial.funext
  intro x
  norm_num [normalizedDerivative, witnessPolynomial, derivativePolynomial,
    Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_pow,
    Polynomial.eval_smul]
  ring

theorem witness_polynomials_proved :
    witnessMatrix.charpoly = witnessPolynomial ∧
    normalizedDerivative 7 witnessMatrix.charpoly = derivativePolynomial ∧
    derivativePolynomial.Monic ∧ derivativePolynomial.natDegree = 6 := by
  exact ⟨witness_charpoly, witness_charpoly ▸ witness_normalizedDerivative,
    derivativePolynomial_monic, derivativePolynomial_degree⟩

end NLA.IS03
