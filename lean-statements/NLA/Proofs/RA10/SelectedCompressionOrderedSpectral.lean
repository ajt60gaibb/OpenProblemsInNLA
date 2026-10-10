import NLA.Proofs.RA10.CustomPSDMathlibBridge
import Mathlib.Analysis.Matrix.PosDef

/-! RA-10: sorted real PSD spectral witnesses for the actual compression.
The source's compression eigenvalue comparison and full target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

noncomputable def sortedHermitianIndex (n : ℕ) : Fin n ≃ Fin n :=
  (Fin.castOrderIso (Fintype.card_fin n).symm).toEquiv.trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))))

theorem mathlibPosSemidef_sortedEigenvalues_antitone {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : Matrix.PosSemidef M) :
    Antitone (fun a : Fin n => hM.1.eigenvalues (sortedHermitianIndex n a)) := by
  intro i j hij
  let t : Fin n ≃o Fin (Fintype.card (Fin n)) :=
    Fin.castOrderIso (Fintype.card_fin n).symm
  have hsort := hM.1.eigenvalues₀_antitone (t.monotone hij)
  simpa [Matrix.IsHermitian.eigenvalues, sortedHermitianIndex, t] using hsort

theorem mathlibPosSemidef_exists_orderedPSD {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : Matrix.PosSemidef M) :
    ∃ (eigenvalues : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ),
      NLA.Statements.RA10.OrderedPSDSpectralDecomposition M eigenvalues Q := by
  classical
  let σ := sortedHermitianIndex n
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
  refine ⟨eigenvalues, Q, ?_, ?_, ?_, ?_⟩
  · intro a
    exact hM.eigenvalues_nonneg (σ a)
  · exact mathlibPosSemidef_sortedEigenvalues_antitone hM
  · intro a b
    have hab := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N (σ a) (σ b)) hUtU
    simpa [Q, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      σ.injective.eq_iff] using hab
  · rw [hMspec]
    ext i j
    simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
    let g : Fin n → ℝ := fun a => hM.1.eigenvalues a * U i a * U j a
    change (∑ a : Fin n, g a) = ∑ a : Fin n, g (σ a)
    exact (σ.sum_comp g).symm

theorem selectedCompression_exists_orderedPSD {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    ∃ (eigenvaluesC : Fin n → ℝ) (QC : Matrix (Fin n) (Fin n) ℝ),
      NLA.Statements.RA10.OrderedPSDSpectralDecomposition
        (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC := by
  exact mathlibPosSemidef_exists_orderedPSD
    (selectedCompression_mathlibPosSemidef (k := k) hA hAhat)

#assert_trust kernel mathlibPosSemidef_sortedEigenvalues_antitone
#assert_trust kernel mathlibPosSemidef_exists_orderedPSD
#assert_trust kernel selectedCompression_exists_orderedPSD
#print axioms selectedCompression_exists_orderedPSD

end NLA.Proofs.RA10
