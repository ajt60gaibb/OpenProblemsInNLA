import NLA.Proofs.RA10.OrderedPSDLoewnerEigenvalue
import NLA.Proofs.RA10.SelectedCompressionOrderedSpectral
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-! RA-10: exact same-index identification of supplied ordered Gram
eigenvalues with the squares of the frozen singular values. This is a
partial nuclear-ideal dependency, not the Eq. (14) bound or Target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Matrix

namespace NLA.Proofs.RA10

private theorem gram_possemidef {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.PosSemidef (Y.transpose * Y) := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self Y

private theorem gram_operator_eq {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toEuclideanLin (Y.transpose * Y) =
      (Matrix.toEuclideanLin Y).adjoint ∘ₗ Matrix.toEuclideanLin Y := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial Y]
  rw [Matrix.toLpLin_mul_same]
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

#assert_trust kernel gram_possemidef
#assert_trust kernel gram_operator_eq

private theorem canonical_ordered_witness {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : Matrix.PosSemidef M) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      NLA.Statements.RA10.OrderedPSDSpectralDecomposition M
        (fun a => hM.1.eigenvalues (NLA.Proofs.RA10.sortedHermitianIndex n a)) Q := by
  classical
  let σ := NLA.Proofs.RA10.sortedHermitianIndex n
  let U : Matrix (Fin n) (Fin n) ℝ := hM.1.eigenvectorUnitary
  let eigenvalues : Fin n → ℝ := fun a => hM.1.eigenvalues (σ a)
  let Q : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i a => U i (σ a)
  have hUtU : U.transpose * U = 1 := by
    have hu := Unitary.coe_star_mul_self hM.1.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hu
  have hMdiag : M = U * Matrix.diagonal hM.1.eigenvalues * U.transpose := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hM.1.spectral_theorem
  have hMspec : M = NLA.Statements.RA10.SpectralMatrix hM.1.eigenvalues U := by
    calc
      M = U * Matrix.diagonal hM.1.eigenvalues * U.transpose := hMdiag
      _ = NLA.Statements.RA10.SpectralMatrix hM.1.eigenvalues U := by
        ext i j
        simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
        rw [Matrix.mul_apply]
        simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
        apply Finset.sum_congr rfl
        intro a _
        ring
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro a
    exact hM.eigenvalues_nonneg (σ a)
  · exact NLA.Proofs.RA10.mathlibPosSemidef_sortedEigenvalues_antitone hM
  · intro a b
    have hab := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N (σ a) (σ b)) hUtU
    simpa [Q, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      σ.injective.eq_iff] using hab
  · change M = NLA.Statements.RA10.SpectralMatrix eigenvalues Q
    calc
      M = NLA.Statements.RA10.SpectralMatrix hM.1.eigenvalues U := hMspec
      _ = NLA.Statements.RA10.SpectralMatrix eigenvalues Q := by
        ext i j
        simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
        let g : Fin n → ℝ := fun a => hM.1.eigenvalues a * U i a * U j a
        change (∑ a : Fin n, g a) = ∑ a : Fin n, g (σ a)
        exact (σ.sum_comp g).symm

#assert_trust kernel canonical_ordered_witness

private theorem zero_psd {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.PositiveSemidefinite (M - M) := by
  simp [NLA.Statements.RA10.PositiveSemidefinite]

private theorem canonical_gram_eig_eq_singular_sq {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (gram_possemidef Y).1.eigenvalues
      (NLA.Proofs.RA10.sortedHermitianIndex n i) =
      (Matrix.toEuclideanLin Y).singularValues i.val ^ 2 := by
  let hM := gram_possemidef Y
  let T := Matrix.toEuclideanLin Y
  let a : Fin (Fintype.card (Fin n)) :=
    (Fin.castOrderIso (Fintype.card_fin n).symm) i
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Fintype.card (Fin n) := finrank_euclideanSpace
  have hOp : Matrix.toEuclideanLin (Y.transpose * Y) = T.adjoint ∘ₗ T :=
    gram_operator_eq Y
  have hindex :
      hM.1.eigenvalues (NLA.Proofs.RA10.sortedHermitianIndex n i) =
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM.1).eigenvalues
          hn a := by
    simp [Matrix.IsHermitian.eigenvalues,
      Matrix.IsHermitian.eigenvalues₀,
      NLA.Proofs.RA10.sortedHermitianIndex, a]
  have heigs :
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM.1).eigenvalues
          hn =
        T.isSymmetric_adjoint_comp_self.eigenvalues hn := by
    apply (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM.1)
      hn T.isSymmetric_adjoint_comp_self hn).2
    exact congrArg LinearMap.charpoly hOp
  rw [hindex]
  rw [heigs]
  simpa [a, Fin.castOrderIso_apply] using (T.sq_singularValues_fin hn a).symm

#assert_trust kernel zero_psd
#assert_trust kernel canonical_gram_eig_eq_singular_sq

theorem orderedPSD_gram_eigenvalue_eq_singular_sq {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) ℝ)
    {g : Fin n → ℝ} {QG : Matrix (Fin n) (Fin n) ℝ}
    (hG : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (Y.transpose * Y) g QG) (i : Fin n) :
    g i = (Matrix.toEuclideanLin Y).singularValues i.val ^ 2 := by
  let hM := gram_possemidef Y
  obtain ⟨Qcan, hcan⟩ := canonical_ordered_witness hM
  have hzero := zero_psd (Y.transpose * Y)
  have hle := NLA.Proofs.RA10.orderedPSDSpectral_eigenvalues_le_of_psd_sub
    hG hcan hzero i
  have hge := NLA.Proofs.RA10.orderedPSDSpectral_eigenvalues_le_of_psd_sub
    hcan hG hzero i
  have heq : g i =
      hM.1.eigenvalues (NLA.Proofs.RA10.sortedHermitianIndex n i) :=
    le_antisymm hge hle
  exact heq.trans (canonical_gram_eig_eq_singular_sq Y i)

#assert_trust kernel orderedPSD_gram_eigenvalue_eq_singular_sq
#print axioms orderedPSD_gram_eigenvalue_eq_singular_sq

end NLA.Proofs.RA10
