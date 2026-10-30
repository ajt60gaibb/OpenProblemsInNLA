import NLA.Proofs.RE06.GaussianLaplace

/-! Finite weighted quadratic Gaussian transforms and Chernoff bounds,
including their transport to the frozen countable Gaussian stream. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open NLA.Computation.NonadaptiveMatrixQuery

namespace NLA.Proofs.RE06

variable {ι : Type*} [Fintype ι]

/-- Unnormalized squared sketch energy after a fixed orthogonal rotation. -/
def gaussianQuadratic (w : ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i, w i * (x i) ^ 2

theorem inv_sqrt_eq_exp_neg_half_log (x : ℝ) (hx : 0 < x) :
    (Real.sqrt x)⁻¹ = Real.exp (-(Real.log x) / 2) := by
  calc
    _ = Real.exp (Real.log (Real.sqrt x)⁻¹) := (Real.exp_log (inv_pos.mpr
      (Real.sqrt_pos.mpr hx))).symm
    _ = _ := by rw [Real.log_inv, Real.log_sqrt hx.le]; congr 1; ring

theorem gaussianQuadratic_exp_integral (w : ι → ℝ) (t : ℝ)
    (hdom : ∀ i, t * w i < 1 / 2) :
    (∫ x : ι → ℝ, Real.exp (t * gaussianQuadratic w x)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∏ i, (Real.sqrt (1 - 2 * (t * w i)))⁻¹ := by
  have heq (x : ι → ℝ) : Real.exp (t * gaussianQuadratic w x) =
      ∏ i, Real.exp ((t * w i) * (x i) ^ 2) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [gaussianQuadratic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [heq]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Real.exp ((t * w i) * x ^ 2))]
  exact Finset.prod_congr rfl (fun i _ => gaussian_square_exp_integral (t * w i) (hdom i))

theorem gaussianQuadratic_exp_integral_log (w : ι → ℝ) (t : ℝ)
    (hdom : ∀ i, t * w i < 1 / 2) :
    (∫ x : ι → ℝ, Real.exp (t * gaussianQuadratic w x)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      Real.exp (-(∑ i, Real.log (1 - 2 * (t * w i))) / 2) := by
  rw [gaussianQuadratic_exp_integral w t hdom]
  calc
    _ = ∏ i, Real.exp (-(Real.log (1 - 2 * (t * w i))) / 2) := by
      apply Finset.prod_congr rfl
      intro i _
      exact inv_sqrt_eq_exp_neg_half_log _ (by linarith [hdom i])
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_div, Finset.sum_neg_distrib]

theorem streamQuadratic_exp_integral (f : ι → ℕ) (hf : Function.Injective f)
    (w : ι → ℝ) (t : ℝ) (hdom : ∀ i, t * w i < 1 / 2) :
    (∫ ω : ℕ → ℝ, Real.exp (t * gaussianQuadratic w (fun i => ω (f i))) ∂GaussianLaw) =
      Real.exp (-(∑ i, Real.log (1 - 2 * (t * w i))) / 2) := by
  have he := (finite_stream_selection_hasLaw f hf).integral_comp
    (f := fun x => Real.exp (t * gaussianQuadratic w x)) (by apply Continuous.aestronglyMeasurable; unfold gaussianQuadratic; fun_prop)
  exact he.trans (gaussianQuadratic_exp_integral_log w t hdom)

theorem streamQuadratic_exp_integrable (f : ι → ℕ) (hf : Function.Injective f)
    (w : ι → ℝ) (t : ℝ) (hdom : ∀ i, t * w i < 1 / 2) :
    Integrable (fun ω : ℕ → ℝ => Real.exp
      (t * gaussianQuadratic w (fun i => ω (f i)))) GaussianLaw := by
  by_contra h
  have he := streamQuadratic_exp_integral f hf w t hdom
  rw [integral_undef h] at he
  exact (Real.exp_ne_zero _).symm he

/-- Actual lower-tail Chernoff bound before optimizing the parameter. -/
theorem streamQuadratic_lower_chernoff (f : ι → ℕ) (hf : Function.Injective f)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (θ : ℝ) (hθ : 0 ≤ θ) (a : ℝ) :
    GaussianLaw.real {ω | gaussianQuadratic w (fun i => ω (f i)) ≤ a} ≤
      Real.exp (θ * a - (∑ i, Real.log (1 + 2 * θ * w i)) / 2) := by
  have hdom : ∀ i, (-θ) * w i < 1 / 2 := by
    intro i
    have := mul_nonneg hθ (hw i)
    nlinarith
  have h := measure_le_le_exp_mul_mgf (μ := GaussianLaw)
    (X := fun ω => gaussianQuadratic w (fun i => ω (f i))) a (neg_nonpos.mpr hθ)
    (streamQuadratic_exp_integrable f hf w (-θ) hdom)
  rw [mgf, streamQuadratic_exp_integral f hf w (-θ) hdom, ← Real.exp_add] at h
  simpa only [mul_neg, neg_mul, sub_neg_eq_add, neg_neg, mul_assoc, sub_eq_add_neg,
    neg_div] using h

/-- Actual upper-tail Chernoff bound on its integrability domain. -/
theorem streamQuadratic_upper_chernoff (f : ι → ℕ) (hf : Function.Injective f)
    (w : ι → ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (hdom : ∀ i, θ * w i < 1 / 2) (a : ℝ) :
    GaussianLaw.real {ω | a ≤ gaussianQuadratic w (fun i => ω (f i))} ≤
      Real.exp (-θ * a - (∑ i, Real.log (1 - 2 * θ * w i)) / 2) := by
  have h := measure_ge_le_exp_mul_mgf (μ := GaussianLaw)
    (X := fun ω => gaussianQuadratic w (fun i => ω (f i))) a hθ
    (streamQuadratic_exp_integrable f hf w θ hdom)
  rw [mgf, streamQuadratic_exp_integral f hf w θ hdom, ← Real.exp_add] at h
  simpa only [mul_assoc, sub_eq_add_neg, neg_div] using h

#assert_trust kernel inv_sqrt_eq_exp_neg_half_log
#assert_trust kernel gaussianQuadratic_exp_integral
#assert_trust kernel gaussianQuadratic_exp_integral_log
#assert_trust kernel streamQuadratic_exp_integral
#assert_trust kernel streamQuadratic_exp_integrable
#assert_trust kernel streamQuadratic_lower_chernoff
#assert_trust kernel streamQuadratic_upper_chernoff
#print axioms inv_sqrt_eq_exp_neg_half_log
#print axioms gaussianQuadratic_exp_integral
#print axioms gaussianQuadratic_exp_integral_log
#print axioms streamQuadratic_exp_integral
#print axioms streamQuadratic_exp_integrable
#print axioms streamQuadratic_lower_chernoff
#print axioms streamQuadratic_upper_chernoff
end NLA.Proofs.RE06
