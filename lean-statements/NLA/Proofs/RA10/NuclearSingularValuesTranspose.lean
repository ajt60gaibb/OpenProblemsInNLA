import NLA.Proofs.RA10.NuclearIdealGramIndex
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! RA-10: exact zero-based singular values of a real square matrix and its
transpose coincide. The summed nuclear transpose and right ideal inequalities
remain separate gates. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Matrix

namespace NLA.Proofs.RA10

private theorem gramPSD_transpose {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.PosSemidef (Y.transpose * Y) := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self Y

private theorem gramOperator_transpose {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toEuclideanLin (Y.transpose * Y) =
      (Matrix.toEuclideanLin Y).adjoint ∘ₗ Matrix.toEuclideanLin Y := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial Y]
  rw [Matrix.toLpLin_mul_same]
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

private theorem canonicalGramEigenvalue_transpose {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (gramPSD_transpose Y).1.eigenvalues
      (sortedHermitianIndex n i) =
      (Matrix.toEuclideanLin Y).singularValues i.val ^ 2 := by
  let hM := gramPSD_transpose Y
  let T := Matrix.toEuclideanLin Y
  let a : Fin (Fintype.card (Fin n)) :=
    (Fin.castOrderIso (Fintype.card_fin n).symm) i
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Fintype.card (Fin n) := finrank_euclideanSpace
  have hOp : Matrix.toEuclideanLin (Y.transpose * Y) = T.adjoint ∘ₗ T :=
    gramOperator_transpose Y
  have hindex :
      hM.1.eigenvalues (sortedHermitianIndex n i) =
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM.1).eigenvalues
          hn a := by
    simp [Matrix.IsHermitian.eigenvalues,
      Matrix.IsHermitian.eigenvalues₀, sortedHermitianIndex, a]
  have heigs :
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM.1).eigenvalues hn =
        T.isSymmetric_adjoint_comp_self.eigenvalues hn := by
    apply (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM.1)
      hn T.isSymmetric_adjoint_comp_self hn).2
    exact congrArg LinearMap.charpoly hOp
  rw [hindex, heigs]
  simpa [a, Fin.castOrderIso_apply] using (T.sq_singularValues_fin hn a).symm

theorem singularValues_transpose_eq {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (Matrix.toEuclideanLin M.transpose).singularValues i.val =
      (Matrix.toEuclideanLin M).singularValues i.val := by
  let hMT := gramPSD_transpose M.transpose
  let hM := gramPSD_transpose M
  have hchar : ((M.transpose).transpose * M.transpose).charpoly =
      (M.transpose * M).charpoly := by
    simpa only [Matrix.transpose_transpose] using
      Matrix.charpoly_mul_comm M M.transpose
  have heig : hMT.1.eigenvalues = hM.1.eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff hMT.1 hM.1).2 hchar
  have hsqT := canonicalGramEigenvalue_transpose M.transpose i
  have hsqM := canonicalGramEigenvalue_transpose M i
  have hsq :
      (Matrix.toEuclideanLin M.transpose).singularValues i.val ^ 2 =
        (Matrix.toEuclideanLin M).singularValues i.val ^ 2 := by
    calc
      _ = hMT.1.eigenvalues (sortedHermitianIndex n i) := hsqT.symm
      _ = hM.1.eigenvalues (sortedHermitianIndex n i) := congrFun heig _
      _ = _ := hsqM
  exact (sq_eq_sq₀
    ((Matrix.toEuclideanLin M.transpose).singularValues_nonneg i.val)
    ((Matrix.toEuclideanLin M).singularValues_nonneg i.val)).mp hsq

#assert_trust kernel canonicalGramEigenvalue_transpose
#assert_trust kernel singularValues_transpose_eq
#print axioms singularValues_transpose_eq

end NLA.Proofs.RA10
