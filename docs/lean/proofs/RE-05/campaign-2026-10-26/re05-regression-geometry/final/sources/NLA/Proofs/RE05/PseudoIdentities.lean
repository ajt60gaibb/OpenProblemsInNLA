/- Adapted from immutable repository commit 181c365dc426875aaa61984c901478b1b7c696e6,
lean-statements/NLA/Proofs/RE06/PseudoInverseIdentities.lean. Only the import/namespace transport and this
provenance header differ; the actual shared pseudoinverse model is unchanged. -/
import NLA.Proofs.RE05.PseudoCore

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery

/-- The four Moore–Penrose equations for a concrete rectangular real matrix. -/
def IsMP {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ)
    (P : Matrix (Fin b) (Fin a) ℝ) : Prop :=
  B * P * B = B ∧ P * B * P = P ∧
    (B * P).transpose = B * P ∧ (P * B).transpose = P * B

theorem sandwich_contract {a b t : ℕ} (U : Matrix (Fin a) (Fin t) ℝ)
    (hU : U.transpose * U = 1) (D E : Matrix (Fin t) (Fin t) ℝ)
    (W : Matrix (Fin t) (Fin b) ℝ) :
    (U * D * U.transpose) * (U * E * W) = U * (D * E) * W := by
  calc
    _ = U * D * (U.transpose * U) * E * W := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem sandwich_diagonal_transpose {a t : ℕ} (U : Matrix (Fin a) (Fin t) ℝ)
    (d : Fin t → ℝ) :
    (U * Matrix.diagonal d * U.transpose).transpose = U * Matrix.diagonal d * U.transpose := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    Matrix.mul_assoc]

theorem mul_pseudoinverse_mul {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    B * pseudoInverse B * B = B := by
  calc
    _ = (thinU B * (Matrix.diagonal (sigma B) * Matrix.diagonal (sigmaInv B)) *
        (thinU B).transpose) *
        (thinU B * Matrix.diagonal (sigma B) * (thinV B).transpose) :=
      congrArg₂ (· * ·) (mul_pseudoinverse B) (reconstruction B)
    _ = thinU B * ((Matrix.diagonal (sigma B) * Matrix.diagonal (sigmaInv B)) *
        Matrix.diagonal (sigma B)) * (thinV B).transpose :=
      sandwich_contract _ (thinU_orthogonal B) _ _ _
    _ = thinU B * Matrix.diagonal (sigma B) * (thinV B).transpose := by
      rw [diagonal_sigma_inv_sigma]
    _ = B := (reconstruction B).symm

theorem pseudoinverse_mul_pseudoinverse {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    pseudoInverse B * B * pseudoInverse B = pseudoInverse B := by
  calc
    _ = (thinV B * (Matrix.diagonal (sigmaInv B) * Matrix.diagonal (sigma B)) *
        (thinV B).transpose) *
        (thinV B * Matrix.diagonal (sigmaInv B) * (thinU B).transpose) :=
      congrArg₂ (· * ·) (pseudoinverse_mul B) (pseudoinverse_decomposition B)
    _ = thinV B * ((Matrix.diagonal (sigmaInv B) * Matrix.diagonal (sigma B)) *
        Matrix.diagonal (sigmaInv B)) * (thinU B).transpose :=
      sandwich_contract _ (thinV_orthogonal B) _ _ _
    _ = thinV B * Matrix.diagonal (sigmaInv B) * (thinU B).transpose := by
      rw [diagonal_inv_sigma_inv]
    _ = pseudoInverse B := (pseudoinverse_decomposition B).symm

theorem mul_pseudoinverse_transpose {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (B * pseudoInverse B).transpose = B * pseudoInverse B := by
  rw [mul_pseudoinverse B, Matrix.diagonal_mul_diagonal]
  exact sandwich_diagonal_transpose _ _

theorem pseudoinverse_mul_transpose {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (pseudoInverse B * B).transpose = pseudoInverse B * B := by
  rw [pseudoinverse_mul B, Matrix.diagonal_mul_diagonal]
  exact sandwich_diagonal_transpose _ _

theorem actual_isMP {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    IsMP B (pseudoInverse B) :=
  ⟨mul_pseudoinverse_mul B, pseudoinverse_mul_pseudoinverse B,
    mul_pseudoinverse_transpose B, pseudoinverse_mul_transpose B⟩

#assert_trust kernel actual_isMP
#print axioms actual_isMP
end NLA.Proofs.RE05.Pseudo
