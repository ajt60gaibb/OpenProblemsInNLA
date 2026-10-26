import NLA.Proofs.RE05.PositiveSVDTrace

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.SVDMachine
open scoped BigOperators Matrix

/-- Positive singular directions of every actual PSD SVD agree on both
sides; no assertion is made about the unconstrained zero directions. -/
theorem validSVD_posSemidef_positive_column {n : ℕ}
    {B U V : Matrix (Fin n) (Fin n) ℝ} {sigma : Fin (min n n) → ℝ}
    (h : ValidSVD B U sigma V) (hB : B.PosSemidef) (j : Fin n)
    (hs : 0 < squareSingularValues sigma j) (i : Fin n) : U i j = V i j := by
  have hd := validSVD_posSemidef_weighted_column h hB j
  have hc : (∑ a : Fin n, U a j * V a j) = 1 := by nlinarith
  have huu : (∑ a : Fin n, (U a j)^2) = 1 := by
    simpa only [pow_two, ↓reduceIte] using h.1 j j
  have hvv : (∑ a : Fin n, (V a j)^2) = 1 := by
    simpa only [pow_two, ↓reduceIte] using h.2.1 j j
  have hsum : (∑ a : Fin n, (U a j - V a j)^2) = 0 := by
    calc
      (∑ a : Fin n, (U a j - V a j)^2) =
        (∑ a : Fin n, (U a j)^2) + (∑ a : Fin n, (V a j)^2) -
          2 * ∑ a : Fin n, U a j * V a j := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = 0 := by rw [huu, hvv, hc]; norm_num
  have hle := Finset.single_le_sum (s := Finset.univ)
    (fun a _ => sq_nonneg (U a j - V a j)) (Finset.mem_univ i)
  rw [hsum] at hle
  nlinarith [sq_nonneg (U i j - V i j)]

theorem validSVD_posSemidef_weighted_entry {n : ℕ}
    {B U V : Matrix (Fin n) (Fin n) ℝ} {sigma : Fin (min n n) → ℝ}
    (h : ValidSVD B U sigma V) (hB : B.PosSemidef) (j i : Fin n) :
    squareSingularValues sigma j * V i j = squareSingularValues sigma j * U i j := by
  by_cases hz : squareSingularValues sigma j = 0
  · simp [hz]
  · rw [validSVD_posSemidef_positive_column h hB j
      (lt_of_le_of_ne (h.2.2.1 _) (Ne.symm hz)) i]

/-- Spectral diagonalization in the full U actually supplied by the literal
SVD relation, with no replacement eigenbasis. -/
theorem validSVD_posSemidef_diagonalization {n : ℕ}
    {B U V : Matrix (Fin n) (Fin n) ℝ} {sigma : Fin (min n n) → ℝ}
    (h : ValidSVD B U sigma V) (hB : B.PosSemidef) :
    B = U * Matrix.diagonal (squareSingularValues sigma) * U.transpose := by
  ext i j
  rw [validSVD_square_reconstruct h]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  calc
    U i k * squareSingularValues sigma k * V j k =
        U i k * (squareSingularValues sigma k * V j k) := by ring
    _ = U i k * (squareSingularValues sigma k * U j k) := by
      rw [validSVD_posSemidef_weighted_entry h hB]
    _ = U i k * squareSingularValues sigma k * U j k := by ring

end NLA.Proofs.RE05
