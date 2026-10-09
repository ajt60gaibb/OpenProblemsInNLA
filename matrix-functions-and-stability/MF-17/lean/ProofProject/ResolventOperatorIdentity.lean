import ProofProject.ResolventConvolution

/-!
# Resolvent identities for strong semigroup kernel operators

The scalar integration-by-parts identity and convolution give exact bounded
operator identities and the derivative/primitive norm bounds used in the source
separator estimates. No unbounded generator or operator-valued integral is used.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ProofProject

/-- Smooth compact support supplies both integrability hypotheses used below. -/
theorem smoothCompact_kernel_integrable {k : ℝ → ℂ}
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    Integrable k ∧ Integrable (deriv k) :=
  ⟨hk.continuous.integrable_of_hasCompactSupport hc,
    (contDiff_infty_iff_deriv.mp hk).2.continuous.integrable_of_hasCompactSupport hc.deriv⟩

namespace BoundedSemigroup

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The exponential average commutes with every scalar kernel operator. -/
theorem resolventAverage_kernelOperator_commute (S : BoundedSemigroup M H)
    (r : ℝ) (hr : 0 < r) {k : ℝ → ℂ} (hi : Integrable k) :
    Commute (S.resolventAverage r hr) (S.kernelOperator k hi) :=
  S.kernelOperator_commute (resolventKernel_integrable hr) hi

/-- Scalar integration by parts becomes the exact resolvent derivative
identity. Positivity of the support removes the lower endpoint contribution. -/
theorem resolventAverage_deriv_identity (S : BoundedSemigroup M H)
    (r : ℝ) (hr : 0 < r) {k : ℝ → ℂ} (hk : ContDiff ℝ ∞ k)
    (hsupp : ∀ s < 0, k s = 0) (hi : Integrable k) (hdi : Integrable (deriv k)) :
    S.resolventAverage r hr * S.kernelOperator (deriv k) hdi =
      (r : ℂ) • (S.kernelOperator k hi -
        S.resolventAverage r hr * S.kernelOperator k hi) := by
  have he := resolventKernel_integrable hr
  have hes : ∀ s < 0, resolventKernel r s = 0 :=
    fun s hs => resolventKernel_of_nonpos r hs.le
  have hds : ∀ s < 0, deriv k s = 0 :=
    fun s hs => deriv_kernel_zero_of_neg hsupp hs
  have hc := kernelConvolution_integrable he hi
  have hcd := kernelConvolution_integrable he hdi
  have hconv : S.kernelOperator (kernelConvolution (resolventKernel r) k) hc =
      S.resolventAverage r hr * S.kernelOperator k hi :=
    S.kernelOperator_convolution he hi hes hsupp
  have hconvd : S.kernelOperator (kernelConvolution (resolventKernel r) (deriv k)) hcd =
      S.resolventAverage r hr * S.kernelOperator (deriv k) hdi :=
    S.kernelOperator_convolution he hdi hes hds
  calc
    _ = S.kernelOperator (kernelConvolution (resolventKernel r) (deriv k)) hcd :=
      hconvd.symm
    _ = (r : ℂ) • S.kernelOperator k hi -
        (r : ℂ) • S.kernelOperator (kernelConvolution (resolventKernel r) k) hc := by
      ext x
      simp only [kernelOperator_apply, sub_apply,
        smul_apply]
      simp_rw [kernelConvolution_resolventKernel_deriv r hk hsupp,
        sub_smul, mul_smul]
      have hir : Integrable (fun s => (r : ℂ) • (k s • S.positiveOrbit x s)) := by
        simpa only [Pi.smul_apply] using! (S.kernelOrbit_integrable hi x).smul (r : ℂ)
      have hcr : Integrable (fun s => (r : ℂ) •
          (kernelConvolution (resolventKernel r) k s • S.positiveOrbit x s)) := by
        simpa only [Pi.smul_apply] using! (S.kernelOrbit_integrable hc x).smul (r : ℂ)
      rw [integral_sub hir hcr, integral_smul, integral_smul]
    _ = _ := by rw [hconv, smul_sub]

/-- Exact identity for the complementary resolvent average. -/
theorem resolventAverage_keep_identity (S : BoundedSemigroup M H)
    (r : ℝ) (hr : 0 < r) {k : ℝ → ℂ} (hk : ContDiff ℝ ∞ k)
    (hsupp : ∀ s < 0, k s = 0) (hi : Integrable k) (hdi : Integrable (deriv k)) :
    (1 - S.resolventAverage r hr) * S.kernelOperator k hi =
      (r : ℂ)⁻¹ • (S.resolventAverage r hr * S.kernelOperator (deriv k) hdi) := by
  have hid : (r : ℂ) • ((1 - S.resolventAverage r hr) * S.kernelOperator k hi) =
      S.resolventAverage r hr * S.kernelOperator (deriv k) hdi := by
    rw [sub_mul, one_mul]
    exact (S.resolventAverage_deriv_identity r hr hk hsupp hi hdi).symm
  rw [← hid, inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr hr.ne')]

/-- Exact primitive-and-remainder identity for a kernel `p' - d`. -/
theorem resolventAverage_kill_identity (S : BoundedSemigroup M H)
    (r : ℝ) (hr : 0 < r) {p d : ℝ → ℂ} (hp : ContDiff ℝ ∞ p)
    (hps : ∀ s < 0, p s = 0) (hpi : Integrable p) (hpdi : Integrable (deriv p))
    (hdi : Integrable d) :
    S.resolventAverage r hr * S.kernelOperator (deriv p - d) (hpdi.sub hdi) =
      (r : ℂ) • ((1 - S.resolventAverage r hr) * S.kernelOperator p hpi) -
        S.resolventAverage r hr * S.kernelOperator d hdi := by
  rw [S.kernelOperator_sub hpdi hdi, mul_sub,
    S.resolventAverage_deriv_identity r hr hp hps hpi hpdi, sub_mul, one_mul]

/-- The high-frequency part is bounded by the derivative kernel, with the exact
factor `M / r`. No nontriviality of the Hilbert space is required. -/
theorem resolventAverage_keep_norm_le (S : BoundedSemigroup M H)
    (r : ℝ) (hr : 0 < r) {k : ℝ → ℂ} (hk : ContDiff ℝ ∞ k)
    (hsupp : ∀ s < 0, k s = 0) (hi : Integrable k) (hdi : Integrable (deriv k)) :
    ‖(1 - S.resolventAverage r hr) * S.kernelOperator k hi‖ ≤
      (M / r) * ‖S.kernelOperator (deriv k) hdi‖ := by
  have hid := S.resolventAverage_deriv_identity r hr hk hsupp hi hdi
  have heq : (r : ℂ) • ((1 - S.resolventAverage r hr) * S.kernelOperator k hi) =
      S.resolventAverage r hr * S.kernelOperator (deriv k) hdi := by
    rw [sub_mul, one_mul]
    exact hid.symm
  have hn := congrArg norm heq
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hn
  have hprod : ‖S.resolventAverage r hr * S.kernelOperator (deriv k) hdi‖ ≤
      M * ‖S.kernelOperator (deriv k) hdi‖ := by
    calc
      _ ≤ ‖S.resolventAverage r hr‖ * ‖S.kernelOperator (deriv k) hdi‖ := norm_mul_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (S.resolventAverage_norm_le r hr)
        (norm_nonneg (S.kernelOperator (deriv k) hdi))
  apply (mul_le_mul_iff_right₀ hr).mp
  calc
    _ ≤ M * ‖S.kernelOperator (deriv k) hdi‖ := hn.le.trans hprod
    _ = _ := by field_simp [hr.ne']

/-- For a decomposition `k = p' - d`, the low-frequency average has a small
primitive term and a remainder term. All integrability assumptions are explicit
and are automatic for smooth compactly supported kernels. -/
theorem resolventAverage_kill_norm_le (S : BoundedSemigroup M H)
    (r : ℝ) (hr : 0 < r) {p d : ℝ → ℂ} (hp : ContDiff ℝ ∞ p)
    (hps : ∀ s < 0, p s = 0) (hpi : Integrable p) (hpdi : Integrable (deriv p))
    (hdi : Integrable d) :
    ‖S.resolventAverage r hr * S.kernelOperator (deriv p - d) (hpdi.sub hdi)‖ ≤
      r * (1 + M) * ‖S.kernelOperator p hpi‖ + M * ‖S.kernelOperator d hdi‖ := by
  have hprod (A : H →L[ℂ] H) : ‖S.resolventAverage r hr * A‖ ≤ M * ‖A‖ := by
    calc
      _ ≤ ‖S.resolventAverage r hr‖ * ‖A‖ := norm_mul_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (S.resolventAverage_norm_le r hr) (norm_nonneg A)
  have hpbound : ‖S.kernelOperator p hpi -
      S.resolventAverage r hr * S.kernelOperator p hpi‖ ≤
      (1 + M) * ‖S.kernelOperator p hpi‖ := by
    calc
      _ ≤ ‖S.kernelOperator p hpi‖ +
          ‖S.resolventAverage r hr * S.kernelOperator p hpi‖ := norm_sub_le _ _
      _ ≤ ‖S.kernelOperator p hpi‖ + M * ‖S.kernelOperator p hpi‖ :=
        add_le_add le_rfl (hprod (S.kernelOperator p hpi))
      _ = _ := by ring
  have hdbound : ‖S.resolventAverage r hr * S.kernelOperator d hdi‖ ≤
      M * ‖S.kernelOperator d hdi‖ :=
    hprod (S.kernelOperator d hdi)
  rw [S.kernelOperator_sub hpdi hdi, mul_sub,
    S.resolventAverage_deriv_identity r hr hp hps hpi hpdi]
  calc
    _ ≤ ‖(r : ℂ) • (S.kernelOperator p hpi -
          S.resolventAverage r hr * S.kernelOperator p hpi)‖ +
        ‖S.resolventAverage r hr * S.kernelOperator d hdi‖ := norm_sub_le _ _
    _ = r * ‖S.kernelOperator p hpi -
          S.resolventAverage r hr * S.kernelOperator p hpi‖ +
        ‖S.resolventAverage r hr * S.kernelOperator d hdi‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    _ ≤ r * ((1 + M) * ‖S.kernelOperator p hpi‖) +
        M * ‖S.kernelOperator d hdi‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hpbound hr.le) hdbound
    _ = _ := by ring

end BoundedSemigroup

end ProofProject
