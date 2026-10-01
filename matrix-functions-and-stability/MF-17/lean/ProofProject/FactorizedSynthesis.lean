import ProofProject.Definitions

/-!
# Applying synthesis bounds twice

A synthesis bound for the adjoints yields the corresponding sum-of-squares
bound for the original operators. Testing on the vectors `X j x` proves this
directly, without constructing a product-space adjoint or a polar decomposition.
-/

noncomputable section

namespace ProofProject

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type v} [Fintype ι]

/-- The adjoint synthesis estimate implies the original analysis estimate.
The argument also covers the empty index type and the constant `D = 0`. -/
theorem adjoint_synthesis_implies_analysis
    (X : ι → H →L[ℂ] H) {D : ℝ} (hD : 0 ≤ D)
    (hX : ∀ y : ι → H,
      ‖∑ j, (X j).adjoint (y j)‖ ^ 2 ≤ D * ∑ j, ‖y j‖ ^ 2) (x : H) :
    (∑ j, ‖X j x‖ ^ 2) ≤ D * ‖x‖ ^ 2 := by
  let E : ℝ := ∑ j, ‖X j x‖ ^ 2
  let z : H := ∑ j, (X j).adjoint (X j x)
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have htest : ‖z‖ ^ 2 ≤ D * E := hX (fun j => X j x)
  have hinner : (inner ℂ x z).re = E := by
    simp only [z, E, inner_sum, ContinuousLinearMap.adjoint_inner_right,
      Complex.re_sum]
    exact Finset.sum_congr rfl fun j _ => inner_self_eq_norm_sq (𝕜 := ℂ) (X j x)
  have hdual : E ≤ ‖x‖ * ‖z‖ := by
    rw [← hinner]
    exact re_inner_le_norm (𝕜 := ℂ) x z
  have hEsq : E * E ≤ E * (D * ‖x‖ ^ 2) := by
    calc
      _ = E ^ 2 := (pow_two E).symm
      _ ≤ (‖x‖ * ‖z‖) ^ 2 := pow_le_pow_left₀ hE0 hdual 2
      _ = ‖x‖ ^ 2 * ‖z‖ ^ 2 := mul_pow _ _ _
      _ ≤ ‖x‖ ^ 2 * (D * E) := mul_le_mul_of_nonneg_left htest (sq_nonneg _)
      _ = _ := by ring
  change E ≤ _
  by_cases hE : E = 0
  · rw [hE]
    exact mul_nonneg hD (sq_nonneg _)
  · exact (mul_le_mul_iff_right₀ (lt_of_le_of_ne hE0 (Ne.symm hE))).mp
      (by simpa only [mul_comm E] using hEsq)

/-- The two synthesis estimates bound each value of the sum of factorizations. -/
theorem factorized_synthesis_apply_sq_le
    (X Y : ι → H →L[ℂ] H) {D : ℝ} (hD : 0 ≤ D)
    (hY : ∀ y : ι → H, ‖∑ j, Y j (y j)‖ ^ 2 ≤ D * ∑ j, ‖y j‖ ^ 2)
    (hX : ∀ y : ι → H,
      ‖∑ j, (X j).adjoint (y j)‖ ^ 2 ≤ D * ∑ j, ‖y j‖ ^ 2) (x : H) :
    ‖∑ j, Y j (X j x)‖ ^ 2 ≤ D ^ 2 * ‖x‖ ^ 2 := by
  calc
    _ ≤ D * ∑ j, ‖X j x‖ ^ 2 := hY (fun j => X j x)
    _ ≤ D * (D * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left
      (adjoint_synthesis_implies_analysis X hD hX x) hD
    _ = _ := by ring

/-- The source's twice-applied synthesis bound. No independence of the ranges
or polar factorization hypothesis is needed for this implication. -/
theorem factorized_synthesis_norm_le
    (X Y : ι → H →L[ℂ] H) {D : ℝ} (hD : 0 ≤ D)
    (hY : ∀ y : ι → H, ‖∑ j, Y j (y j)‖ ^ 2 ≤ D * ∑ j, ‖y j‖ ^ 2)
    (hX : ∀ y : ι → H,
      ‖∑ j, (X j).adjoint (y j)‖ ^ 2 ≤ D * ∑ j, ‖y j‖ ^ 2) :
    ‖∑ j, (Y j).comp (X j)‖ ≤ D := by
  apply ContinuousLinearMap.opNorm_le_bound _ hD
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (norm_nonneg x))).mp
  simpa only [sum_apply, ContinuousLinearMap.comp_apply, mul_pow] using
    factorized_synthesis_apply_sq_le X Y hD hY hX x

end ProofProject
