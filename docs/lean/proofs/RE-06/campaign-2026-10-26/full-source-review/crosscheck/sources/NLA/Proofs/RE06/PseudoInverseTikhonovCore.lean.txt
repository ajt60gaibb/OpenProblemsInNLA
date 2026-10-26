import NLA.Proofs.RE06.PseudoInverseMeasurable

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE06.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery

def tikhonov {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) (t : ℝ) : Matrix (Fin b) (Fin a) ℝ :=
  B.transpose * (B * B.transpose + t • (1 : Matrix (Fin a) (Fin a) ℝ))⁻¹

def regularizedSigma {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) (t : ℝ) : Fin (min a b) → ℝ :=
  fun k => sigma B k / ((sigma B k) ^ 2 + t)

theorem transpose_reconstruction {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    B.transpose = thinV B * Matrix.diagonal (sigma B) * (thinU B).transpose := by
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    Matrix.mul_assoc] using congrArg Matrix.transpose (reconstruction B)

theorem gram_decomposition {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    B * B.transpose = thinU B *
      (Matrix.diagonal (sigma B) * Matrix.diagonal (sigma B)) * (thinU B).transpose := by
  calc
    _ = (thinU B * Matrix.diagonal (sigma B) * (thinV B).transpose) *
        (thinV B * Matrix.diagonal (sigma B) * (thinU B).transpose) :=
      congrArg₂ (· * ·) (reconstruction B) (transpose_reconstruction B)
    _ = thinU B * Matrix.diagonal (sigma B) * ((thinV B).transpose * thinV B) *
        Matrix.diagonal (sigma B) * (thinU B).transpose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [thinV_orthogonal]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem regularized_diagonal_identity {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ)
    (t : ℝ) (ht : 0 < t) :
    Matrix.diagonal (regularizedSigma B t) *
        (Matrix.diagonal (sigma B) * Matrix.diagonal (sigma B)) +
      t • Matrix.diagonal (regularizedSigma B t) = Matrix.diagonal (sigma B) := by
  simp only [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
    dsimp [regularizedSigma]
    have hden : (sigma B i) ^ 2 + t ≠ 0 := by nlinarith [sq_nonneg (sigma B i)]
    field_simp
    <;> ring
  · simp [Matrix.add_apply, Matrix.diagonal_apply, Matrix.smul_apply, hij]

theorem regularized_gram_isUnit {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ)
    (t : ℝ) (ht : 0 < t) : IsUnit (B * B.transpose + t • (1 : Matrix (Fin a) (Fin a) ℝ)).det := by
  have hgram : (B * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose B
  have hpos : (t • (1 : Matrix (Fin a) (Fin a) ℝ)).PosDef := Matrix.PosDef.one.smul ht
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.PosDef.isUnit (Matrix.PosDef.posSemidef_add hgram hpos))

theorem regularized_solution {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ)
    (t : ℝ) (ht : 0 < t) :
    (thinV B * Matrix.diagonal (regularizedSigma B t) * (thinU B).transpose) *
      (B * B.transpose + t • (1 : Matrix (Fin a) (Fin a) ℝ)) = B.transpose := by
  calc
    _ = (thinV B * Matrix.diagonal (regularizedSigma B t) * (thinU B).transpose) *
        (thinU B * (Matrix.diagonal (sigma B) * Matrix.diagonal (sigma B)) * (thinU B).transpose) +
        t • (thinV B * Matrix.diagonal (regularizedSigma B t) * (thinU B).transpose) := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
      exact congrArg (fun G =>
        (thinV B * Matrix.diagonal (regularizedSigma B t) * (thinU B).transpose) * G +
          t • (thinV B * Matrix.diagonal (regularizedSigma B t) * (thinU B).transpose))
        (gram_decomposition B)
    _ = thinV B * (Matrix.diagonal (regularizedSigma B t) *
        (Matrix.diagonal (sigma B) * Matrix.diagonal (sigma B))) * (thinU B).transpose +
        t • (thinV B * Matrix.diagonal (regularizedSigma B t) * (thinU B).transpose) := by
      congr 1
      calc
        _ = thinV B * Matrix.diagonal (regularizedSigma B t) *
            ((thinU B).transpose * thinU B) *
            (Matrix.diagonal (sigma B) * Matrix.diagonal (sigma B)) * (thinU B).transpose := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [thinU_orthogonal]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = thinV B * (Matrix.diagonal (regularizedSigma B t) *
        (Matrix.diagonal (sigma B) * Matrix.diagonal (sigma B)) +
          t • Matrix.diagonal (regularizedSigma B t)) * (thinU B).transpose := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = thinV B * Matrix.diagonal (sigma B) * (thinU B).transpose := by
      rw [regularized_diagonal_identity B t ht]
    _ = B.transpose := (transpose_reconstruction B).symm

theorem tikhonov_decomposition {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ)
    (t : ℝ) (ht : 0 < t) :
    tikhonov B t = thinV B * Matrix.diagonal (regularizedSigma B t) * (thinU B).transpose := by
  unfold tikhonov
  have h := congrArg
    (fun X => X * (B * B.transpose + t • (1 : Matrix (Fin a) (Fin a) ℝ))⁻¹)
    (regularized_solution B t ht)
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (regularized_gram_isUnit B t ht),
    Matrix.mul_one] at h
  exact h.symm

#assert_trust kernel tikhonov_decomposition
#print axioms tikhonov_decomposition
end NLA.Proofs.RE06.Pseudo
