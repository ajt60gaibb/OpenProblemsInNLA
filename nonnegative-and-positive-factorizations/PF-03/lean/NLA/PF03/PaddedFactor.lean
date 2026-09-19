import NLA.PF03.ConePointed
import NLA.PF03.SeedOrthogonal

/-! C22: five literal zero rows give the required relative-boundary witness.
No dimension444 assertion or explicit facet enumeration is needed. All real
nonnegativity comes from the whole-cone H-representation and actual seed columns.
Sidney Holden: original mathematics. George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology: formalization;
Codex assistance. Author: /root. -/
set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

lemma castMatrix_transpose {m n : ℕ} (A : QMat m n) :
    castMatrix Aᵀ = (castMatrix A)ᵀ := rfl

lemma padRows_left {N : ℕ} (R : QMat N 7) (i : Fin N) :
    padRows R (Fin.castAdd 5 i) = R i := by
  exact Fin.append_left R (0 : QMat 5 7) i

lemma padRows_right {N : ℕ} (R : QMat N 7) (i : Fin 5) :
    padRows R (Fin.natAdd N i) = 0 := by
  exact Fin.append_right R (0 : QMat 5 7) i

lemma pad_mulVec_left {N : ℕ} (R : QMat N 7) (x : Fin 7 → ℝ) (i : Fin N) :
    ((castMatrix (padRows R)).mulVec x) (Fin.castAdd 5 i) =
      ((castMatrix R).mulVec x) i := by
  simp only [Matrix.mulVec, dotProduct, castMatrix, Matrix.map_apply, padRows_left]

lemma pad_mulVec_right {N : ℕ} (R : QMat N 7) (x : Fin 7 → ℝ) (i : Fin 5) :
    ((castMatrix (padRows R)).mulVec x) (Fin.natAdd N i) = 0 := by
  simp only [Matrix.mulVec, dotProduct, castMatrix, Matrix.map_apply,
    padRows_right, Pi.zero_apply, Rat.cast_zero, zero_mul, Finset.sum_const_zero]

lemma padded_HSet {N : ℕ} (R : QMat N 7) : HSet (padRows R) = HSet R := by
  ext x
  constructor
  · intro h i
    simpa only [pad_mulVec_left] using h (Fin.castAdd 5 i)
  · intro h i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa only [pad_mulVec_left] using h a
    · simp only [pad_mulVec_right, le_refl]

lemma padded_kernel {N : ℕ} (R : QMat N 7) (x : Fin 7 → ℝ) :
    (castMatrix (padRows R)).mulVec x = 0 ↔ (castMatrix R).mulVec x = 0 := by
  constructor
  · intro h
    funext i
    simpa only [pad_mulVec_left, Pi.zero_apply] using congrFun h (Fin.castAdd 5 i)
  · intro h
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa only [pad_mulVec_left, Pi.zero_apply] using congrFun h a
    · exact pad_mulVec_right R x b

theorem padded_real_factor {N : ℕ} (R : QMat N 7) (hR : HSet R = K) :
    5 ≤ N + 5 ∧
      (paddedGram R).val (paddedIndex N) (paddedIndex N) = 0 ∧
      (∀ i j, 0 ≤ paddedRealFactor R i j) ∧
      (realCast (paddedGram R)).val = paddedRealFactor R * (paddedRealFactor R)ᵀ ∧
      HSet (padRows R) = K ∧
      (∀ x : Fin 7 → ℝ,
        (castMatrix (padRows R)).mulVec x = 0 ↔ (castMatrix R).mulVec x = 0) := by
  refine ⟨by omega, ?_, ?_, ?_, (padded_HSet R).trans hR, padded_kernel R⟩
  · change (padRows R * (padRows R)ᵀ) (paddedIndex N) (paddedIndex N) = 0
    simp only [Matrix.mul_apply, Matrix.transpose_apply, paddedIndex, padRows_right,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  · intro i j
    have hseed : seedColumn j ∈ HSet (padRows R) := by
      rw [padded_HSet R, hR]
      exact seedColumn_mem_K j
    exact hseed i
  · change castMatrix (padRows R * (padRows R)ᵀ) =
      (castMatrix (padRows R) * orthogonalSeed) *
        (castMatrix (padRows R) * orthogonalSeed)ᵀ
    rw [castMatrix_mul, castMatrix_transpose, Matrix.transpose_mul]
    have hO : orthogonalSeed * orthogonalSeedᵀ = 1 := seed_orthogonal.2.1
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc orthogonalSeed orthogonalSeedᵀ,
      hO, Matrix.one_mul]

#print axioms padded_real_factor
#assert_trust kernel padded_real_factor
end NLA.PF03
