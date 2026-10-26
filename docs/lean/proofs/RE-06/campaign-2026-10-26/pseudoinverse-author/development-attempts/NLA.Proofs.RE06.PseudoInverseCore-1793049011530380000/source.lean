import NLA.Proofs.RE06.SVDTotal

/-! Algebra of the actual SVD-defined RE-06 pseudoinverse. Thin singular-vector
matrices retain zero singular values, so every identity includes rank-deficient
and empty-dimensional matrices. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators

namespace NLA.Proofs.RE06.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery

def thinU {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    Matrix (Fin a) (Fin (min a b)) ℝ :=
  fun i k => (exactSVD B).U i (Fin.castLE (Nat.min_le_left a b) k)

def thinV {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    Matrix (Fin b) (Fin (min a b)) ℝ :=
  fun i k => (exactSVD B).V i (Fin.castLE (Nat.min_le_right a b) k)

def sigma {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) : Fin (min a b) → ℝ :=
  (exactSVD B).sigma

def sigmaInv {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) : Fin (min a b) → ℝ :=
  fun k => if sigma B k = 0 then 0 else (sigma B k)⁻¹

theorem thinU_orthogonal {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (thinU B).transpose * thinU B = 1 := by
  ext i j
  have h := (svd_total a b B).1
    (Fin.castLE (Nat.min_le_left a b) i) (Fin.castLE (Nat.min_le_left a b) j)
  simpa [Matrix.mul_apply, thinU] using h

theorem thinV_orthogonal {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (thinV B).transpose * thinV B = 1 := by
  ext i j
  have h := (svd_total a b B).2.1
    (Fin.castLE (Nat.min_le_right a b) i) (Fin.castLE (Nat.min_le_right a b) j)
  simpa [Matrix.mul_apply, thinV] using h

theorem reconstruction {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    B = thinU B * Matrix.diagonal (sigma B) * (thinV B).transpose := by
  ext i j
  simpa [Matrix.mul_apply, Matrix.mul_diagonal, thinU, thinV, sigma] using
    (svd_total a b B).2.2.2.2 i j

theorem pseudoinverse_decomposition {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    pseudoInverse B = thinV B * Matrix.diagonal (sigmaInv B) * (thinU B).transpose := by
  ext i j
  simp only [pseudoInverse, Matrix.mul_apply, Matrix.mul_diagonal,
    Matrix.transpose_apply, thinV, thinU, sigmaInv, sigma]
  rfl

theorem diagonal_sigma_inv_sigma {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    Matrix.diagonal (sigma B) * Matrix.diagonal (sigmaInv B) * Matrix.diagonal (sigma B) =
      Matrix.diagonal (sigma B) := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : sigma B k = 0 <;> simp [sigmaInv, h, mul_assoc]

theorem diagonal_inv_sigma_inv {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    Matrix.diagonal (sigmaInv B) * Matrix.diagonal (sigma B) * Matrix.diagonal (sigmaInv B) =
      Matrix.diagonal (sigmaInv B) := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : sigma B k = 0 <;> simp [sigmaInv, h, mul_assoc]

theorem diagonal_sigma_inv_commute {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    Matrix.diagonal (sigma B) * Matrix.diagonal (sigmaInv B) =
      Matrix.diagonal (sigmaInv B) * Matrix.diagonal (sigma B) := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

theorem mul_pseudoinverse {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    B * pseudoInverse B = thinU B *
      (Matrix.diagonal (sigma B) * Matrix.diagonal (sigmaInv B)) * (thinU B).transpose := by
  rw [reconstruction B, pseudoinverse_decomposition B]
  calc
    _ = thinU B * Matrix.diagonal (sigma B) *
        ((thinV B).transpose * thinV B) * Matrix.diagonal (sigmaInv B) *
        (thinU B).transpose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [thinV_orthogonal]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem pseudoinverse_mul {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    pseudoInverse B * B = thinV B *
      (Matrix.diagonal (sigmaInv B) * Matrix.diagonal (sigma B)) * (thinV B).transpose := by
  rw [reconstruction B, pseudoinverse_decomposition B]
  calc
    _ = thinV B * Matrix.diagonal (sigmaInv B) *
        ((thinU B).transpose * thinU B) * Matrix.diagonal (sigma B) *
        (thinV B).transpose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [thinU_orthogonal]; simp only [Matrix.mul_one, Matrix.mul_assoc]

#assert_trust kernel reconstruction
#assert_trust kernel pseudoinverse_decomposition
#assert_trust kernel mul_pseudoinverse
#assert_trust kernel pseudoinverse_mul
#print axioms pseudoinverse_mul
end NLA.Proofs.RE06.Pseudo
