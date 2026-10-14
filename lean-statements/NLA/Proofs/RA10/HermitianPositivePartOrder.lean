import NLA.Proofs.RA10.HermitianPositivePart

/-! Positive-part order facts for the actual spectral positive part.
These are unconditional finite-dimensional matrix lemmas, including singular
matrices and dimension zero. They do not assert the full RA-10 target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA10

theorem hermitianPositivePart_posSemidef {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    Matrix.PosSemidef (hermitianPositivePart M) := by
  classical
  rw [hermitianPositivePart, dif_pos hM]
  have hd : Matrix.PosSemidef
      (Matrix.diagonal (fun i : Fin n => max (hM.eigenvalues i) 0)) :=
    Matrix.PosSemidef.diagonal (fun i => le_max_right (hM.eigenvalues i) 0)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same
      (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)

theorem hermitianPositivePart_sub_posSemidef {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    Matrix.PosSemidef (hermitianPositivePart M - M) := by
  classical
  let U : Matrix (Fin n) (Fin n) ℝ := hM.eigenvectorUnitary
  let d : Fin n → ℝ := hM.eigenvalues
  have hMdiag : M = U * Matrix.diagonal d * U.transpose := by
    simpa [U, d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hM.spectral_theorem
  have hpart : hermitianPositivePart M =
      U * Matrix.diagonal (fun i : Fin n => max (d i) 0) * U.transpose := by
    simp only [hermitianPositivePart, dif_pos hM]
    rfl
  have hdiff : hermitianPositivePart M - M =
      U * Matrix.diagonal (fun i : Fin n => max (d i) 0 - d i) *
        U.transpose := by
    rw [hpart, hMdiag, ← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
  rw [hdiff]
  have hd : Matrix.PosSemidef
      (Matrix.diagonal (fun i : Fin n => max (d i) 0 - d i)) :=
    Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (le_max_left (d i) 0))
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same U

#assert_trust kernel hermitianPositivePart_posSemidef
#assert_trust kernel hermitianPositivePart_sub_posSemidef
#print axioms hermitianPositivePart_sub_posSemidef

end NLA.Proofs.RA10
