import NLA.Proofs.RA10.SelectedCompressionEigenvalue
import NLA.Proofs.RA10.OrderedSpectralIntersection

/-! RA-10 positive compression prefix support in the actual selected
projector range. The min-max eigenvalue comparison and full target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

theorem orderedPSDSpectral_reconstruct_vector {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hM : NLA.Statements.RA10.OrderedPSDSpectralDecomposition M eigenvalues Q)
    (x : Fin n → ℝ) (i : Fin n) :
    x i = ∑ b : Fin n, (∑ j : Fin n, x j * Q j b) * Q i b := by
  have hQTQ : Q.transpose * Q = 1 := by
    ext u v
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      hM.2.2.1 u v
  have hQQT : Q * Q.transpose = 1 := mul_eq_one_comm.mp hQTQ
  have hx : x = Q *ᵥ (Q.transpose *ᵥ x) := by
    calc
      x = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x := (Matrix.one_mulVec x).symm
      _ = (Q * Q.transpose) *ᵥ x := by rw [hQQT]
      _ = Q *ᵥ (Q.transpose *ᵥ x) := by rw [Matrix.mulVec_mulVec]
  have hcoord (b : Fin n) : (Q.transpose *ᵥ x) b =
      ∑ j : Fin n, x j * Q j b := by
    rw [Matrix.mulVec_apply_eq_sum]
    simp only [Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    x i = ∑ b : Fin n, Q i b * (Q.transpose *ᵥ x) b := by
      simpa [Matrix.mulVec_apply_eq_sum] using congrFun hx i
    _ = ∑ b : Fin n, (∑ j : Fin n, x j * Q j b) * Q i b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [hcoord]
      ring

theorem selectedCompression_positivePrefix_supported {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    (a : Fin n) (ha : 0 < eigenvaluesC a)
    (x : Fin n → ℝ)
    (hx : ∀ b : Fin n, a.val < b.val → (∑ i : Fin n, x i * QC i b) = 0) :
    selectedProjection k QAhat *ᵥ x = x := by
  classical
  let P := selectedProjection k QAhat
  let coord : Fin n → ℝ := fun b => ∑ i : Fin n, x i * QC i b
  have hrepr : x = ∑ b : Fin n, coord b • QC.col b := by
    ext i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] using
      orderedPSDSpectral_reconstruct_vector hC x i
  have hsupported (b : Fin n) (hb : b.val ≤ a.val) :
      P *ᵥ QC.col b = QC.col b := by
    have hpos : 0 < eigenvaluesC b :=
      lt_of_lt_of_le ha (hC.2.1 (Fin.le_iff_val_le_val.mpr hb))
    have h := selectedCompression_positiveEigenvector_supported (k := k) hAhat hC b hpos
    change P *ᵥ QC.col b = QC.col b at h
    exact h
  have hmap : P *ᵥ (∑ b : Fin n, coord b • QC.col b) =
      ∑ b : Fin n, coord b • (P *ᵥ QC.col b) := by
    change P.mulVecLin (∑ b : Fin n, coord b • QC.col b) =
      ∑ b : Fin n, coord b • P.mulVecLin (QC.col b)
    simp only [map_sum, map_smul]
  calc
    P *ᵥ x = P *ᵥ (∑ b : Fin n, coord b • QC.col b) := by rw [hrepr]
    _ = ∑ b : Fin n, coord b • (P *ᵥ QC.col b) := hmap
    _ = ∑ b : Fin n, coord b • QC.col b := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : b.val ≤ a.val
      · rw [hsupported b hb]
      · have hzero : coord b = 0 := hx b (lt_of_not_ge hb)
        simp [hzero]
    _ = x := hrepr.symm

#assert_trust kernel orderedPSDSpectral_reconstruct_vector
#assert_trust kernel selectedCompression_positivePrefix_supported
#print axioms selectedCompression_positivePrefix_supported

end NLA.Proofs.RA10
