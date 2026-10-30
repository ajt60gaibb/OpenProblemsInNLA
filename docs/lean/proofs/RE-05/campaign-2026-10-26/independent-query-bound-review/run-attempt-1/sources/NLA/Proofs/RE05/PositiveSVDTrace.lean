import NLA.Proofs.RE05.SVDTotal

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.SVDMachine
open scoped BigOperators Matrix

/-- The exact square reindex used by the unchanged query model. -/
def squareSingularValues {n : ℕ} (sigma : Fin (min n n) → ℝ) (j : Fin n) : ℝ :=
  sigma (Fin.cast (Nat.min_self n).symm j)

theorem validSVD_square_reconstruct {n : ℕ} {B U V : Matrix (Fin n) (Fin n) ℝ}
    {sigma : Fin (min n n) → ℝ} (h : ValidSVD B U sigma V) (i j : Fin n) :
    B i j = ∑ k : Fin n, U i k * squareSingularValues sigma k * V j k := by
  rw [h.2.2.2.2 i j]
  apply Fintype.sum_equiv (finCongr (Nat.min_self n))
  intro k
  simp only [squareSingularValues, finCongr_apply]
  congr 2

theorem validSVD_square_mulVec_right {n : ℕ} {B U V : Matrix (Fin n) (Fin n) ℝ}
    {sigma : Fin (min n n) → ℝ} (h : ValidSVD B U sigma V) (j : Fin n) :
    B *ᵥ (fun a => V a j) = fun i => squareSingularValues sigma j * U i j := by
  ext i
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [validSVD_square_reconstruct h]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ k : Fin n, ∑ a : Fin n,
      U i k * squareSingularValues sigma k * V a k * V a j) =
        ∑ k : Fin n, U i k * squareSingularValues sigma k *
          (∑ a : Fin n, V a k * V a j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = squareSingularValues sigma j * U i j := by
      simp_rw [h.2.1]
      simp [mul_comm]

theorem validSVD_square_transpose_mulVec_left {n : ℕ}
    {B U V : Matrix (Fin n) (Fin n) ℝ} {sigma : Fin (min n n) → ℝ}
    (h : ValidSVD B U sigma V) (j : Fin n) :
    B.transpose *ᵥ (fun a => U a j) =
      fun i => squareSingularValues sigma j * V i j := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  simp_rw [validSVD_square_reconstruct h]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ k : Fin n, ∑ a : Fin n,
      U a k * squareSingularValues sigma k * V i k * U a j) =
        ∑ k : Fin n, squareSingularValues sigma k * V i k *
          (∑ a : Fin n, U a k * U a j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = squareSingularValues sigma j * V i j := by
      simp_rw [h.1]
      simp

/-- Positivity forces the weighted left/right column inner product to be
the singular value, including the zero singular-value case. -/
theorem validSVD_posSemidef_weighted_column {n : ℕ}
    {B U V : Matrix (Fin n) (Fin n) ℝ} {sigma : Fin (min n n) → ℝ}
    (h : ValidSVD B U sigma V) (hB : B.PosSemidef) (j : Fin n) :
    squareSingularValues sigma j * (∑ i : Fin n, U i j * V i j) =
      squareSingularValues sigma j := by
  let u : Fin n → ℝ := fun i => U i j
  let v : Fin n → ℝ := fun i => V i j
  let s := squareSingularValues sigma j
  let c := ∑ i : Fin n, u i * v i
  have hsym : B.transpose = B := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hB.1
  have hu : B *ᵥ u = fun i => s * v i := by
    simpa only [hsym, u, v, s] using validSVD_square_transpose_mulVec_left h j
  have hv : B *ᵥ v = fun i => s * u i := validSVD_square_mulVec_right h j
  have hw : B *ᵥ (u - v) = fun i => -s * (u i - v i) := by
    rw [Matrix.mulVec_sub, hu, hv]
    ext i
    simp only [Pi.sub_apply]
    ring
  have hq := hB.dotProduct_mulVec_nonneg (u - v)
  rw [hw] at hq
  have hq' : 0 ≤ -s * ∑ i : Fin n, (u i - v i)^2 := by
    calc
      0 ≤ star (u - v) ⬝ᵥ (fun i => -s * (u i - v i)) := hq
      _ = -s * ∑ i : Fin n, (u i - v i)^2 := by
        simp only [dotProduct, Pi.star_apply, star_trivial, Pi.sub_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have huu : (∑ i : Fin n, (u i)^2) = 1 := by
    simpa only [u, pow_two, ↓reduceIte] using h.1 j j
  have hvv : (∑ i : Fin n, (v i)^2) = 1 := by
    simpa only [v, pow_two, ↓reduceIte] using h.2.1 j j
  have hsquares : (∑ i : Fin n, (u i - v i)^2) = 2 - 2 * c := by
    calc
      (∑ i : Fin n, (u i - v i)^2) =
        (∑ i : Fin n, (u i)^2) + (∑ i : Fin n, (v i)^2) -
          2 * ∑ i : Fin n, u i * v i := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 2 - 2 * c := by rw [huu, hvv]; ring
  have hss : 0 ≤ 2 - 2 * c := by
    rw [← hsquares]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs : 0 ≤ s := h.2.2.1 _
  rw [hsquares] at hq'
  change s * c = s
  nlinarith [mul_nonneg hs hss]

/-- Every literal legal full SVD of a PSD square matrix has singular-value
sum equal to the actual trace, independently of tied or zero-vector bases. -/
theorem validSVD_posSemidef_trace {n : ℕ}
    {B U V : Matrix (Fin n) (Fin n) ℝ} {sigma : Fin (min n n) → ℝ}
    (h : ValidSVD B U sigma V) (hB : B.PosSemidef) :
    B.trace = ∑ j : Fin n, squareSingularValues sigma j := by
  change (∑ i : Fin n, B i i) = _
  simp_rw [validSVD_square_reconstruct h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ i : Fin n, U i j * squareSingularValues sigma j * V i j) =
        squareSingularValues sigma j * ∑ i : Fin n, U i j * V i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = squareSingularValues sigma j := validSVD_posSemidef_weighted_column h hB j

#assert_trust kernel validSVD_square_reconstruct
#assert_trust kernel validSVD_square_mulVec_right
#assert_trust kernel validSVD_square_transpose_mulVec_left
#assert_trust kernel validSVD_posSemidef_weighted_column
#assert_trust kernel validSVD_posSemidef_trace
#print axioms validSVD_posSemidef_trace
end NLA.Proofs.RE05
