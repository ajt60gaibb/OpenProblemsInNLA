import NLA.Proofs.RA10.NuclearIdealOperatorBridge
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-! RA-10: left orthogonal invariance of the frozen all-singular-value nuclear norm.
This is one generic dependency; right invariance, triangle, ideal inequalities,
pinching, and the final Target remain open. -/

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

private theorem euclideanLin_transpose_eq_adjoint {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toEuclideanLin M.transpose = (Matrix.toEuclideanLin M).adjoint := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint M

private theorem euclideanLin_gram_mul_left_orthogonal {n : ℕ}
    (U X : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.transpose * U = 1) :
    (Matrix.toEuclideanLin (U * X)).adjoint ∘ₗ Matrix.toEuclideanLin (U * X) =
      (Matrix.toEuclideanLin X).adjoint ∘ₗ Matrix.toEuclideanLin X := by
  rw [← euclideanLin_transpose_eq_adjoint (U * X),
    ← euclideanLin_transpose_eq_adjoint X,
    ← toEuclideanLin_mul_exact,
    ← toEuclideanLin_mul_exact]
  congr 1
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem nuclearNorm_orthogonal_left {n : ℕ}
    (U X : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.transpose * U = 1) :
    NLA.Statements.RA10.NuclearNorm (U * X) =
      NLA.Statements.RA10.NuclearNorm X := by
  unfold NLA.Statements.RA10.NuclearNorm
  have hgram := euclideanLin_gram_mul_left_orthogonal U X hU
  apply Finset.sum_congr rfl
  intro i _
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  rw [(Matrix.toEuclideanLin (U * X)).singularValues_fin hn i,
    (Matrix.toEuclideanLin X).singularValues_fin hn i]
  have heig :=
    (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff
      (Matrix.toEuclideanLin (U * X)).isSymmetric_adjoint_comp_self hn
      (Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self hn).2
      (congrArg LinearMap.charpoly hgram)
  exact congrArg Real.sqrt (congrFun heig i)

#assert_trust kernel euclideanLin_transpose_eq_adjoint
#assert_trust kernel euclideanLin_gram_mul_left_orthogonal
#assert_trust kernel nuclearNorm_orthogonal_left
#print axioms nuclearNorm_orthogonal_left

end NLA.Proofs.RA10
