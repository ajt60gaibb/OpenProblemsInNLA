import NLA.Statements.RA10
import Mathlib.Tactic.Ring

/-! RA-10 Gate 1a: the frozen entrywise spectral reconstruction has exactly
the expected quadratic form and is positive semidefinite. This is a partial
bridge, not a proof of the frozen constant-eleven transfer target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

theorem spectralMatrix_quadratic_form {n : ℕ}
    (eigenvalues : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      x i * NLA.Statements.RA10.SpectralMatrix eigenvalues Q i j * x j) =
      ∑ a : Fin n, eigenvalues a * (∑ i : Fin n, x i * Q i a) ^ 2 := by
  have hentry (i j : Fin n) :
      x i * NLA.Statements.RA10.SpectralMatrix eigenvalues Q i j * x j =
        ∑ a : Fin n, eigenvalues a * (x i * Q i a) * (x j * Q j a) := by
    simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      x i * NLA.Statements.RA10.SpectralMatrix eigenvalues Q i j * x j)
        = ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n,
            eigenvalues a * (x i * Q i a) * (x j * Q j a) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              exact hentry i j
    _ = ∑ i : Fin n, ∑ a : Fin n, ∑ j : Fin n,
          eigenvalues a * (x i * Q i a) * (x j * Q j a) := by
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_comm
    _ = ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          eigenvalues a * (x i * Q i a) * (x j * Q j a) := Finset.sum_comm
    _ = ∑ a : Fin n,
          eigenvalues a * (∑ i : Fin n, x i * Q i a) ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _
            simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring

theorem orderedPSDSpectralDecomposition_positiveSemidefinite {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    NLA.Statements.RA10.PositiveSemidefinite A := by
  rcases h with ⟨hvalues, _, _, hA⟩
  rw [hA]
  constructor
  · intro i j
    simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro a _
    ring
  · intro x
    rw [spectralMatrix_quadratic_form]
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (hvalues a) (sq_nonneg _)

#assert_trust kernel spectralMatrix_quadratic_form
#assert_trust kernel orderedPSDSpectralDecomposition_positiveSemidefinite
#print axioms orderedPSDSpectralDecomposition_positiveSemidefinite

end NLA.Proofs.RA10
