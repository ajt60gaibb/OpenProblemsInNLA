import NLA.Proofs.RA10.NuclearIdealOperatorBridge
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! RA-10: right orthogonal invariance of the frozen all-singular-value
nuclear norm. This proves only a generic matrix fact; pinching, ideal bounds,
and the final Target remain open. -/

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

private theorem euclideanLin_transpose_eq_adjoint_right {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toEuclideanLin M.transpose = (Matrix.toEuclideanLin M).adjoint := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint M

private theorem euclideanLin_gram_eq_matrix {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.toEuclideanLin M).adjoint ∘ₗ Matrix.toEuclideanLin M =
      Matrix.toEuclideanLin (M.transpose * M) := by
  rw [toEuclideanLin_mul_exact, euclideanLin_transpose_eq_adjoint_right]

private theorem euclideanLin_charpoly_eq_matrix {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.toEuclideanLin M).charpoly = M.charpoly := by
  simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.charpoly_toLin]

private theorem gram_charpoly_mul_right_orthogonal {n : ℕ}
    (X U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U * U.transpose = 1) :
    ((Matrix.toEuclideanLin (X * U)).adjoint ∘ₗ
        Matrix.toEuclideanLin (X * U)).charpoly =
      ((Matrix.toEuclideanLin X).adjoint ∘ₗ
        Matrix.toEuclideanLin X).charpoly := by
  rw [euclideanLin_gram_eq_matrix, euclideanLin_gram_eq_matrix,
    euclideanLin_charpoly_eq_matrix, euclideanLin_charpoly_eq_matrix]
  have hgram : (X * U).transpose * (X * U) =
      (U.transpose * (X.transpose * X)) * U := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hgram]
  calc
    ((U.transpose * (X.transpose * X)) * U).charpoly =
        (U * (U.transpose * (X.transpose * X))).charpoly :=
      Matrix.charpoly_mul_comm _ _
    _ = (X.transpose * X).charpoly := by
      rw [← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem nuclearNorm_orthogonal_right {n : ℕ}
    (X U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U * U.transpose = 1) :
    NLA.Statements.RA10.NuclearNorm (X * U) =
      NLA.Statements.RA10.NuclearNorm X := by
  unfold NLA.Statements.RA10.NuclearNorm
  have hchar := gram_charpoly_mul_right_orthogonal X U hU
  apply Finset.sum_congr rfl
  intro i _
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  rw [(Matrix.toEuclideanLin (X * U)).singularValues_fin hn i,
    (Matrix.toEuclideanLin X).singularValues_fin hn i]
  have heig :=
    (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff
      (Matrix.toEuclideanLin (X * U)).isSymmetric_adjoint_comp_self hn
      (Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self hn).2 hchar
  exact congrArg Real.sqrt (congrFun heig i)

#assert_trust kernel euclideanLin_transpose_eq_adjoint_right
#assert_trust kernel euclideanLin_gram_eq_matrix
#assert_trust kernel euclideanLin_charpoly_eq_matrix
#assert_trust kernel gram_charpoly_mul_right_orthogonal
#assert_trust kernel nuclearNorm_orthogonal_right
#print axioms nuclearNorm_orthogonal_right

end NLA.Proofs.RA10
