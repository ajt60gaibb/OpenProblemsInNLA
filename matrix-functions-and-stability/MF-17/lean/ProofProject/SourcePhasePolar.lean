import ProofProject.SourcePhaseDefs

/-!
# Exact boundary phase from principal polar factors

The phase is computed through an explicit logarithmic exponent of the source
factor, without selecting a global argument of that factor itself.
-/

noncomputable section

namespace ProofProject

@[simp] lemma sourceCircle_re (θ : ℝ) : (sourceCircle θ).re = Real.cos θ := by
  simp [sourceCircle, Complex.exp_re]

@[simp] lemma sourceCircle_im (θ : ℝ) : (sourceCircle θ).im = Real.sin θ := by
  simp [sourceCircle, Complex.exp_im]

lemma sourceCircle_one_add_polar (θ : ℝ) :
    1 + sourceCircle θ = ((2 * Real.cos (θ / 2) : ℝ) : ℂ) *
      (Complex.cos ((θ / 2 : ℝ) : ℂ) + Complex.sin ((θ / 2 : ℝ) : ℂ) * Complex.I) := by
  have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    simpa only [show 2 * (θ / 2) = θ by ring] using Real.cos_two_mul (θ / 2)
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    simpa only [show 2 * (θ / 2) = θ by ring] using Real.sin_two_mul (θ / 2)
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    sourceCircle_re, sourceCircle_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, mul_zero, zero_mul, mul_one,
    zero_add, add_zero, sub_zero] <;> nlinarith

lemma sourceCircle_one_sub_polar (θ : ℝ) :
    1 - sourceCircle θ = ((2 * Real.sin (θ / 2) : ℝ) : ℂ) *
      (Complex.cos (((θ / 2 - Real.pi / 2) : ℝ) : ℂ) +
        Complex.sin (((θ / 2 - Real.pi / 2) : ℝ) : ℂ) * Complex.I) := by
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    simpa only [show 2 * (θ / 2) = θ by ring] using Real.cos_two_mul_eq_one_sub (θ / 2)
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    simpa only [show 2 * (θ / 2) = θ by ring] using Real.sin_two_mul (θ / 2)
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.sub_re, Complex.sub_im, sourceCircle_re, sourceCircle_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, mul_zero, zero_mul, mul_one,
    zero_add, add_zero, sub_zero, Real.cos_sub, Real.sin_sub,
    Real.cos_pi_div_two, Real.sin_pi_div_two] <;> nlinarith

lemma sourceCircle_half_sin_pos {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    0 < Real.sin (θ / 2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

lemma sourceCircle_half_cos_pos {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    0 < Real.cos (θ / 2) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩

lemma norm_one_add_sourceCircle {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    ‖1 + sourceCircle θ‖ = 2 * Real.cos (θ / 2) := by
  rw [sourceCircle_one_add_polar, norm_mul, Complex.norm_cos_add_sin_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num) (sourceCircle_half_cos_pos hθ0 hθπ))]

lemma norm_one_sub_sourceCircle {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    ‖1 - sourceCircle θ‖ = 2 * Real.sin (θ / 2) := by
  rw [sourceCircle_one_sub_polar, norm_mul, Complex.norm_cos_add_sin_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num) (sourceCircle_half_sin_pos hθ0 hθπ))]

lemma arg_one_add_sourceCircle {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    (1 + sourceCircle θ).arg = θ / 2 := by
  rw [sourceCircle_one_add_polar]
  exact Complex.arg_mul_cos_add_sin_mul_I
    (mul_pos (by norm_num) (sourceCircle_half_cos_pos hθ0 hθπ))
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

lemma arg_one_sub_sourceCircle {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    (1 - sourceCircle θ).arg = -((Real.pi - θ) / 2) := by
  rw [sourceCircle_one_sub_polar]
  have h := Complex.arg_mul_cos_add_sin_mul_I
    (mul_pos (by norm_num : (0 : ℝ) < 2) (sourceCircle_half_sin_pos hθ0 hθπ))
    (show θ / 2 - Real.pi / 2 ∈ Set.Ioc (-Real.pi) Real.pi from
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  convert h using 1
  ring

lemma one_add_sourceCircle_ne_zero {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    1 + sourceCircle θ ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_one_add_sourceCircle hθ0 hθπ]
  exact (mul_pos (by norm_num) (sourceCircle_half_cos_pos hθ0 hθπ)).ne'

lemma one_sub_sourceCircle_ne_zero {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    1 - sourceCircle θ ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_one_sub_sourceCircle hθ0 hθπ]
  exact (mul_pos (by norm_num) (sourceCircle_half_sin_pos hθ0 hθπ)).ne'

lemma sourceCayley_sourceCircle_ne_zero {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    sourceCayley (sourceCircle θ) ≠ 0 :=
  div_ne_zero (one_add_sourceCircle_ne_zero hθ0 hθπ) (one_sub_sourceCircle_ne_zero hθ0 hθπ)

lemma sourceCayley_sourceCircle_im (θ : ℝ) :
    (sourceCayley (sourceCircle θ)).im =
      2 * Real.sin θ / Complex.normSq (1 - sourceCircle θ) := by
  rw [sourceCayley, Complex.div_im]
  simp [sourceCircle_im, sourceCircle_re]
  ring

lemma arg_sourceCayley_sourceCircle {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    (sourceCayley (sourceCircle θ)).arg = Real.pi / 2 := by
  apply Complex.arg_eq_pi_div_two_iff.mpr
  constructor
  · rw [sourceCayley_re, Complex.normSq_eq_norm_sq, norm_sourceCircle]
    norm_num
  · rw [sourceCayley_sourceCircle_im]
    exact div_pos (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ))
      (Complex.normSq_pos.mpr (one_sub_sourceCircle_ne_zero hθ0 hθπ))

lemma one_add_sourceCircle_mem_slitPlane {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    1 + sourceCircle θ ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff_arg.mpr
  refine ⟨?_, one_add_sourceCircle_ne_zero hθ0 hθπ⟩
  rw [arg_one_add_sourceCircle hθ0 hθπ]
  linarith [Real.pi_pos]

lemma one_sub_sourceCircle_mem_slitPlane {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    1 - sourceCircle θ ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff_arg.mpr
  refine ⟨?_, one_sub_sourceCircle_ne_zero hθ0 hθπ⟩
  rw [arg_one_sub_sourceCircle hθ0 hθπ]
  linarith [Real.pi_pos]

lemma sourceCayley_sourceCircle_mem_slitPlane {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    sourceCayley (sourceCircle θ) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff_arg.mpr
  refine ⟨?_, sourceCayley_sourceCircle_ne_zero hθ0 hθπ⟩
  rw [arg_sourceCayley_sourceCircle hθ0 hθπ]
  linarith [Real.pi_pos]

lemma sourceWeightFactor_circle_ne_zero (α : ℝ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) : sourceWeightFactor α (sourceCircle θ) ≠ 0 := by
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (sourceCayley_sourceCircle_ne_zero hθ0 hθπ))
  · exact Complex.exp_ne_zero _

/-- A logarithmic exponent for the source factor; it need not be the principal
logarithm of the complete factor. -/
def sourceBoundaryExponent (α θ : ℝ) : ℂ :=
  Complex.log (sourceCayley (sourceCircle θ)) * ((α / 2 : ℝ) : ℂ) +
    sourceWeightCorrection α (sourceCircle θ)

lemma sourceWeightFactor_circle_eq_exp (α : ℝ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    sourceWeightFactor α (sourceCircle θ) = Complex.exp (sourceBoundaryExponent α θ) := by
  rw [sourceWeightFactor, Complex.cpow_def_of_ne_zero
    (sourceCayley_sourceCircle_ne_zero hθ0 hθπ), ← Complex.exp_add]
  rfl

/-- The double imaginary part of this exponent is exactly β minus the inward
correction. No assertion about the principal argument of ψ is made. -/
lemma sourceBoundaryExponent_two_im (α : ℝ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    2 * (sourceBoundaryExponent α θ).im =
      Real.pi * α / 2 - sourcePhaseCorrection α θ := by
  simp only [sourceBoundaryExponent, Complex.add_im, Complex.mul_im,
    Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add, Complex.log_im,
    arg_sourceCayley_sourceCircle hθ0 hθπ, sourceWeightCorrection,
    Complex.sub_im, Complex.cpow_ofReal_im, norm_one_sub_sourceCircle hθ0 hθπ,
    norm_one_add_sourceCircle hθ0 hθπ, arg_one_sub_sourceCircle hθ0 hθπ,
    arg_one_add_sourceCircle hθ0 hθπ, neg_mul, Real.sin_neg, sourcePhaseCorrection]
  simp only [mul_comm]
  ring

/-- Taking the real part of a conjugate exponential ratio avoids logarithmic
branch choices entirely. -/
lemma re_conj_exp_div_exp (w : ℂ) :
    (starRingEnd ℂ (Complex.exp w) / Complex.exp w).re = Real.cos (2 * w.im) := by
  rw [← Complex.exp_conj, ← Complex.exp_sub, Complex.exp_re]
  simp only [Complex.sub_re, Complex.conj_re, sub_self, Real.exp_zero, one_mul,
    Complex.sub_im, Complex.conj_im]
  rw [show -w.im - w.im = -(2 * w.im) by ring, Real.cos_neg]

/-- The exact boundary phase formula on the open upper semicircle. -/
theorem sourceBoundaryPhase_re (α : ℝ) {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    (sourceBoundaryPhase α θ).re =
      Real.cos (Real.pi * α / 2 - sourcePhaseCorrection α θ) := by
  rw [sourceBoundaryPhase, sourceWeightFactor_circle_eq_exp α hθ0 hθπ,
    re_conj_exp_div_exp, sourceBoundaryExponent_two_im α hθ0 hθπ]

lemma sourceCircle_neg (θ : ℝ) : sourceCircle (-θ) = starRingEnd ℂ (sourceCircle θ) := by
  simp [sourceCircle, ← Complex.exp_conj]

/-- Reflection from the upper to the lower semicircle conjugates ψ. -/
lemma sourceWeightFactor_circle_neg (α : ℝ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    sourceWeightFactor α (sourceCircle (-θ)) =
      starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) := by
  rw [sourceCircle_neg]
  exact sourceWeightFactor_conj_of_mem_slitPlane α
    (sourceCayley_sourceCircle_mem_slitPlane hθ0 hθπ)
    (one_sub_sourceCircle_mem_slitPlane hθ0 hθπ)
    (one_add_sourceCircle_mem_slitPlane hθ0 hθπ)

lemma sourceBoundaryPhase_neg (α : ℝ) {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    sourceBoundaryPhase α (-θ) = starRingEnd ℂ (sourceBoundaryPhase α θ) := by
  simp only [sourceBoundaryPhase, sourceWeightFactor_circle_neg α hθ0 hθπ,
    map_div₀, starRingEnd_self_apply]

lemma sourceBoundaryPhase_re_neg (α : ℝ) {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    (sourceBoundaryPhase α (-θ)).re = (sourceBoundaryPhase α θ).re := by
  rw [sourceBoundaryPhase_neg α hθ0 hθπ, Complex.conj_re]

end ProofProject
