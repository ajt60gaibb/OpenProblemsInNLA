import NLA.Proofs.RA10.SpectralQuadratic
import Mathlib.Tactic.Ring

/-! RA-10 exact Parseval and Rayleigh inequalities in every supplied
ordered real PSD eigenbasis. The min-max intersection, compression
eigenvalue comparison and full transfer target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

theorem orderedPSDSpectral_parseval {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hM : NLA.Statements.RA10.OrderedPSDSpectralDecomposition M eigenvalues Q)
    (x : Fin n → ℝ) :
    (∑ i : Fin n, x i ^ 2) =
      ∑ b : Fin n, (∑ i : Fin n, x i * Q i b) ^ 2 := by
  have hQTQ : Q.transpose * Q = 1 := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      hM.2.2.1 i j
  have hQQT : Q * Q.transpose = 1 := mul_eq_one_comm.mp hQTQ
  let y := Q.transpose *ᵥ x
  have hy (b : Fin n) : y b = ∑ i : Fin n, x i * Q i b := by
    dsimp [y]
    rw [Matrix.mulVec_apply_eq_sum]
    simp only [Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdot : x ⬝ᵥ x = y ⬝ᵥ y := by
    calc
      x ⬝ᵥ x = x ⬝ᵥ ((Q * Q.transpose) *ᵥ x) := by
        rw [hQQT, Matrix.one_mulVec]
      _ = x ⬝ᵥ (Q *ᵥ (Q.transpose *ᵥ x)) := by
        rw [Matrix.mulVec_mulVec]
      _ = (x ᵥ* Q) ⬝ᵥ (Q.transpose *ᵥ x) := by
        rw [Matrix.dotProduct_mulVec]
      _ = y ⬝ᵥ y := by
        have hvec : x ᵥ* Q = y := by
          simpa [y] using (Matrix.vecMul_transpose Q.transpose x)
        rw [hvec]
  simpa only [dotProduct, ← pow_two, hy] using hdot

theorem orderedPSDSpectral_rayleigh_lower_prefix {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hM : NLA.Statements.RA10.OrderedPSDSpectralDecomposition M eigenvalues Q)
    (a : Fin n) (x : Fin n → ℝ)
    (hx : ∀ b : Fin n, a.val < b.val → (∑ i : Fin n, x i * Q i b) = 0) :
    eigenvalues a * (∑ i : Fin n, x i ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j := by
  let coord : Fin n → ℝ := fun b => ∑ i : Fin n, x i * Q i b
  have hparseval := orderedPSDSpectral_parseval hM x
  have hquad := spectralMatrix_quadratic_form eigenvalues Q x
  rw [← hM.2.2.2] at hquad
  calc
    eigenvalues a * (∑ i : Fin n, x i ^ 2) =
        ∑ b : Fin n, eigenvalues a * coord b ^ 2 := by
      rw [hparseval, Finset.mul_sum]
    _ ≤ ∑ b : Fin n, eigenvalues b * coord b ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : b.val ≤ a.val
      · have hle : eigenvalues a ≤ eigenvalues b :=
          hM.2.1 (Fin.le_iff_val_le_val.mpr hb)
        exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      · have hzero : coord b = 0 := hx b (lt_of_not_ge hb)
        simp [hzero]
    _ = ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j := hquad.symm

theorem orderedPSDSpectral_rayleigh_upper_suffix {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (hM : NLA.Statements.RA10.OrderedPSDSpectralDecomposition M eigenvalues Q)
    (a : Fin n) (x : Fin n → ℝ)
    (hx : ∀ b : Fin n, b.val < a.val → (∑ i : Fin n, x i * Q i b) = 0) :
    (∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j) ≤
      eigenvalues a * (∑ i : Fin n, x i ^ 2) := by
  let coord : Fin n → ℝ := fun b => ∑ i : Fin n, x i * Q i b
  have hparseval := orderedPSDSpectral_parseval hM x
  have hquad := spectralMatrix_quadratic_form eigenvalues Q x
  rw [← hM.2.2.2] at hquad
  calc
    (∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j) =
        ∑ b : Fin n, eigenvalues b * coord b ^ 2 := hquad
    _ ≤ ∑ b : Fin n, eigenvalues a * coord b ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : b.val < a.val
      · have hzero : coord b = 0 := hx b hb
        simp [hzero]
      · have hle : eigenvalues b ≤ eigenvalues a :=
          hM.2.1 (Fin.le_iff_val_le_val.mpr (not_lt.mp hb))
        exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    _ = eigenvalues a * (∑ i : Fin n, x i ^ 2) := by
      rw [hparseval, Finset.mul_sum]

#assert_trust kernel orderedPSDSpectral_parseval
#assert_trust kernel orderedPSDSpectral_rayleigh_lower_prefix
#assert_trust kernel orderedPSDSpectral_rayleigh_upper_suffix
#print axioms orderedPSDSpectral_rayleigh_upper_suffix

end NLA.Proofs.RA10
