import NLA.Proofs.RE06.GaussianQuadratic
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

/-- Actual upper-tail Chernoff bound on its integrability domain. -/
theorem streamQuadratic_upper_chernoff {ι : Type*} [Fintype ι]
    (f : ι → ℕ) (hf : Function.Injective f) (w : ι → ℝ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hdom : ∀ (i : ι), θ * w i < (1 / 2 : ℝ)) (a : ℝ) :
    GaussianLaw.real {ω : ℕ → ℝ | a ≤ gaussianQuadratic w (fun i => ω (f i))} ≤
      Real.exp (-θ * a - (∑ i : ι, Real.log (1 - 2 * θ * w i)) / 2) := by
  have hi : Integrable (fun ω : ℕ → ℝ =>
      Real.exp (θ * gaussianQuadratic w (fun i => ω (f i)))) GaussianLaw :=
    streamQuadratic_exp_integrable f hf w θ hdom
  have h := measure_ge_le_exp_mul_mgf (μ := GaussianLaw) (t := θ)
    (X := fun (ω : ℕ → ℝ) => gaussianQuadratic w (fun i => ω (f i))) a hθ hi
  rw [mgf, streamQuadratic_exp_integral f hf w θ hdom, ← Real.exp_add] at h
  simpa only [mul_assoc, sub_eq_add_neg, neg_div] using h

#assert_trust kernel streamQuadratic_upper_chernoff
#print axioms streamQuadratic_upper_chernoff
end NLA.Proofs.RE06
