import ProofProject.Definitions

/-!
# The Hilbert-space phase deficit identity

A norm-preserving phase image `u` of `a`, and an orthogonal complementary vector
`b`, yield the exact deficit identity used to control the weighted projection.
The argument is purely Hilbert-space algebra and introduces no integral premise.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The defect of the phase image relative to the scalar center `μ`. -/
def phaseDefect (μ : ℝ) (a u : H) : ℝ :=
  (1 - μ ^ 2) * ‖a‖ ^ 2 - ‖u - μ • a‖ ^ 2

/-- The algebraic phase identity before normalizing the projection constant. -/
theorem phase_norm_sq_identity (μ : ℝ) (a b u : H)
    (hab : inner ℂ a b = 0) (hu : ‖u‖ = ‖a‖) :
    ‖u + b‖ ^ 2 - μ ^ 2 * ‖a‖ ^ 2 =
      ‖b + (u - μ • a)‖ ^ 2 + phaseDefect μ a u := by
  have hba : inner ℂ b a = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) b a, hab]
    simp
  have hcross : inner ℂ b (u - μ • a) = inner ℂ b u := by
    simp [hba]
  rw [norm_add_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), hcross]
  rw [inner_re_symm u b, hu]
  unfold phaseDefect
  ring

/-- The exact source projection identity, with `μ=1/M`. -/
theorem phase_projection_identity {M : ℝ} (hM : 0 < M) (a b u : H)
    (hab : inner ℂ a b = 0) (hu : ‖u‖ = ‖a‖) :
    M ^ 2 * ‖u + b‖ ^ 2 - ‖a‖ ^ 2 =
      M ^ 2 * (‖b + (u - M⁻¹ • a)‖ ^ 2 + phaseDefect M⁻¹ a u) := by
  rw [← phase_norm_sq_identity M⁻¹ a b u hab hu]
  field_simp

/-- The defect is controlled by the normalized projection deficit. Its sign
is irrelevant for this consequence of the exact identity. -/
theorem phaseDefect_le_div_deficit {M : ℝ} (hM : 0 < M) (a b u : H)
    (hab : inner ℂ a b = 0) (hu : ‖u‖ = ‖a‖) :
    phaseDefect M⁻¹ a u ≤ (M ^ 2 * ‖u + b‖ ^ 2 - ‖a‖ ^ 2) / M ^ 2 := by
  rw [phase_projection_identity hM a b u hab hu]
  rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 hM.ne')]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- A nonnegative phase defect proves the projection estimate with the exact
constant `M`. -/
theorem phase_projection_norm_le {M : ℝ} (hM : 0 < M) (a b u : H)
    (hab : inner ℂ a b = 0) (hu : ‖u‖ = ‖a‖)
    (hδ : 0 ≤ phaseDefect M⁻¹ a u) : ‖a‖ ≤ M * ‖u + b‖ := by
  have hnonneg : 0 ≤ M ^ 2 * ‖u + b‖ ^ 2 - ‖a‖ ^ 2 := by
    rw [phase_projection_identity hM a b u hab hu]
    exact mul_nonneg (sq_nonneg M) (add_nonneg (sq_nonneg _) hδ)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM.le (norm_nonneg _))).mp
  rw [mul_pow]
  linarith

end ProofProject
