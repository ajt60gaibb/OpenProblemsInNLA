import OAI.Analysis.DirectCrouzeix.Duality

namespace OAI

universe u_46

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem norm_entry_le_l2_opNorm {ι : Type u_46} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ ι := EuclideanSpace.single j 1
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
  have he : ‖e‖ = 1 := by simp [e]
  have hij : (T e) i = A i j := by
    change (A *ᵥ Pi.single j 1) i = _
    rw [Matrix.mulVec_single_one]
    rfl
  calc
    ‖A i j‖ = ‖(T e) i‖ := congrArg norm hij.symm
    _ ≤ ‖T e‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm _
    _ = ‖A‖ := by simp [T, he, Matrix.l2_opNorm_toEuclideanCLM]

def sharpnessMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 2; 0, 0]

def sharpnessCoefficients : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ := ![0, 1]

theorem norm_le_one_of_mem_sharpnessRange {z : ℂ}
    (hz : z ∈ numericalRange sharpnessMatrix) : ‖z‖ ≤ 1 := by
  obtain ⟨u, hu, rfl⟩ := hz
  have hsum : ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 = 1 := by
    simpa [hu, Fin.sum_univ_two] using (EuclideanSpace.norm_sq_eq u).symm
  have hev : inner ℂ u
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) sharpnessMatrix u) =
      2 * star (u 0) * u 1 := by
    simp [sharpnessMatrix, EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.ofLp_toEuclideanCLM, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  rw [hev]
  simp only [norm_mul, norm_star]
  norm_num
  nlinarith [sq_nonneg (‖u 0‖ - ‖u 1‖)]

@[simp] theorem sharpness_polynomialValue (z : ℂ) :
    polynomialValue (d := 1) sharpnessCoefficients z = z • 1 := by
  simp [polynomialValue, sharpnessCoefficients, Fin.sum_univ_two]

@[simp] theorem sharpness_tensorEvaluation :
    tensorEvaluation (d := 1) sharpnessMatrix sharpnessCoefficients =
      sharpnessMatrix ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp [tensorEvaluation, sharpnessCoefficients, Fin.sum_univ_two]

theorem sharpness_rangeMaximum_le_one :
    rangeMaximum (d := 1) sharpnessMatrix sharpnessCoefficients ≤ 1 := by
  obtain ⟨z, hz, he⟩ := rangeMaximum_attained (by norm_num : 0 < 2)
    sharpnessMatrix (d := 1) sharpnessCoefficients
  rw [← he, sharpness_polynomialValue, norm_smul, norm_one, mul_one]
  exact norm_le_one_of_mem_sharpnessRange hz

theorem sharpness_tensor_norm_ge_two :
    2 ≤ ‖tensorEvaluation (d := 1) sharpnessMatrix sharpnessCoefficients‖ := by
  have h := norm_entry_le_l2_opNorm
    (sharpnessMatrix ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ)) (0, 0) (1, 0)
  rw [sharpness_tensorEvaluation]
  simpa [sharpnessMatrix, Matrix.kroneckerMap_apply] using h

theorem uniform_sharpness (c : ℝ) (hc : UniversalBound c) : 2 ≤ c := by
  have hmain := hc 2 1 1 (by norm_num) (by norm_num) sharpnessMatrix sharpnessCoefficients
  have hmax := sharpness_rangeMaximum_le_one
  have hlower := sharpness_tensor_norm_ge_two
  have hnonneg : 0 ≤ rangeMaximum (d := 1) sharpnessMatrix sharpnessCoefficients := by
    obtain ⟨z, hz, he⟩ := rangeMaximum_attained (by norm_num : 0 < 2)
      sharpnessMatrix (d := 1) sharpnessCoefficients
    rw [← he]
    exact norm_nonneg _
  have hcpos : 0 ≤ c := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hn) hnonneg
    linarith
  have hmul := mul_le_mul_of_nonneg_left hmax hcpos
  linarith

end DirectCrouzeix

end

end OAI
