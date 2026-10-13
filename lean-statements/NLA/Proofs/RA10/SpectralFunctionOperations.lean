import NLA.Proofs.RA10.SelectedSpectralNuclear

/-! Linearity and constant functions for the frozen spectral sums. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open NLA.Statements.RA10

namespace NLA.Proofs.RA10

theorem functionMatrix_congr {n : ℕ} {f g : ℝ → ℝ} (a : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (h : ∀ i, f (a i) = g (a i)) :
    FunctionMatrix f a Q = FunctionMatrix g a Q := by
  unfold FunctionMatrix
  congr 1
  exact funext h

theorem functionTruncation_congr {n : ℕ} (k : ℕ) {f g : ℝ → ℝ} (a : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (h : ∀ i, f (a i) = g (a i)) :
    FunctionTruncation k f a Q = FunctionTruncation k g a Q := by
  ext i j
  simp only [FunctionTruncation, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [h l]

theorem functionMatrix_add {n : ℕ} (f g : ℝ → ℝ) (a : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    FunctionMatrix (fun x => f x + g x) a Q = FunctionMatrix f a Q + FunctionMatrix g a Q := by
  ext i j
  simp [FunctionMatrix, SpectralMatrix, add_mul, Finset.sum_add_distrib]

theorem functionMatrix_smul {n : ℕ} (c : ℝ) (f : ℝ → ℝ) (a : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    FunctionMatrix (fun x => c * f x) a Q = c • FunctionMatrix f a Q := by
  ext i j
  simp [FunctionMatrix, SpectralMatrix, Finset.mul_sum, mul_assoc]

theorem functionTruncation_add {n : ℕ} (k : ℕ) (f g : ℝ → ℝ) (a : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    FunctionTruncation k (fun x => f x + g x) a Q =
      FunctionTruncation k f a Q + FunctionTruncation k g a Q := by
  ext i j
  simp only [FunctionTruncation, Matrix.of_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> ring

theorem functionTruncation_smul {n : ℕ} (k : ℕ) (c : ℝ) (f : ℝ → ℝ) (a : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    FunctionTruncation k (fun x => c * f x) a Q = c • FunctionTruncation k f a Q := by
  ext i j
  simp only [FunctionTruncation, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> ring

theorem functionMatrix_const {n : ℕ} (c : ℝ) (a : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, ∑ l, Q l i * Q l j = if i = j then 1 else 0) :
    FunctionMatrix (fun _ => c) a Q = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hQtQ : Q.transpose * Q = 1 := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hQ i j
  have hdiag : Matrix.diagonal (fun _ : Fin n => c) =
      c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [FunctionMatrix, spectralMatrix_factor, hdiag]
  simp [mul_eq_one_comm.mp hQtQ]

#assert_trust kernel functionMatrix_add
#assert_trust kernel functionMatrix_congr
#assert_trust kernel functionTruncation_congr
#assert_trust kernel functionMatrix_smul
#assert_trust kernel functionTruncation_add
#assert_trust kernel functionTruncation_smul
#assert_trust kernel functionMatrix_const

end NLA.Proofs.RA10
