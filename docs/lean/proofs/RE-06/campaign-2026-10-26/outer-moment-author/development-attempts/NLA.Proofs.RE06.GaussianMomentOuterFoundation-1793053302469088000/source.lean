import NLA.Proofs.RE06.GaussianMomentTransport

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory

namespace NLA.Proofs.RE06.GaussianMoment

theorem nonnegative_prod_integrable_of_inner_majorant
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) (ν : Measure Γ) [SFinite ν]
    (V : Ω × Γ → ℝ) (hVm : Measurable V) (hV0 : ∀ z, 0 ≤ V z)
    (M : Ω → ℝ) (hM : Integrable M μ)
    (hVi : ∀ᵐ g ∂μ, Integrable (fun h => V (g,h)) ν)
    (hmean : ∀ᵐ g ∂μ, (∫ h, V (g,h) ∂ν) ≤ M g) :
    Integrable V (μ.prod ν) := by
  apply (integrable_prod_iff hVm.aestronglyMeasurable).mpr
  refine ⟨hVi, ?_⟩
  apply hM.mono_nonneg hVm.aestronglyMeasurable.norm.integral_prod_right'
  · exact Filter.Eventually.of_forall (fun g => integral_nonneg (fun h => norm_nonneg _))
  · filter_upwards [hmean] with g hg
    have he : (fun h => ‖V (g,h)‖) = (fun h => V (g,h)) :=
      funext (fun h => Real.norm_of_nonneg (hV0 (g,h)))
    rw [he]
    exact hg

theorem nonnegative_prod_integral_le_inner_majorant
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) (ν : Measure Γ) [SFinite ν]
    (V : Ω × Γ → ℝ) (hVm : Measurable V) (hV0 : ∀ z, 0 ≤ V z)
    (M : Ω → ℝ) (hM : Integrable M μ)
    (hVi : ∀ᵐ g ∂μ, Integrable (fun h => V (g,h)) ν)
    (hmean : ∀ᵐ g ∂μ, (∫ h, V (g,h) ∂ν) ≤ M g) :
    (∫ z, V z ∂μ.prod ν) ≤ ∫ g, M g ∂μ := by
  have hi := nonnegative_prod_integrable_of_inner_majorant μ ν V hVm hV0 M hM hVi hmean
  rw [integral_prod _ hi]
  exact integral_mono_ae hi.integral_prod_left hM hmean

theorem excess_prod_integrable_and_integral_le
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) (ν : Measure Γ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (hXi : Integrable X μ) (V : Ω × Γ → ℝ)
    (hVm : Measurable V) (hV0 : ∀ z, 0 ≤ V z)
    (a b tail : ℝ) (hb : 0 ≤ b) (hXa : (∫ g, X g ∂μ) ≤ a * tail)
    (hVi : ∀ᵐ g ∂μ, Integrable (fun h => V (g,h)) ν)
    (hVb : ∀ᵐ g ∂μ, (∫ h, V (g,h) ∂ν) ≤ b * (tail + X g)) :
    Integrable (fun z => X z.1 + V z) (μ.prod ν) ∧
      (∫ z, X z.1 + V z ∂μ.prod ν) ≤ (a + b + a * b) * tail := by
  have hM : Integrable (fun g => b * (tail + X g)) μ :=
    ((integrable_const tail).add hXi).const_mul b
  have hVi' := nonnegative_prod_integrable_of_inner_majorant μ ν V hVm hV0 _ hM hVi hVb
  have hVbound := nonnegative_prod_integral_le_inner_majorant μ ν V hVm hV0 _ hM hVi hVb
  have hXp := hXi.comp_fst ν
  refine ⟨hXp.add hVi', ?_⟩
  have hXint : (∫ z : Ω × Γ, X z.1 ∂μ.prod ν) = ∫ g, X g ∂μ := by
    rw [integral_prod _ hXp]
    simp
  calc
    _ = (∫ g, X g ∂μ) + ∫ z, V z ∂μ.prod ν := by
      rw [integral_add hXp hVi', hXint]
    _ ≤ (∫ g, X g ∂μ) + ∫ g, b * (tail + X g) ∂μ := add_le_add_left hVbound _
    _ = (∫ g, X g ∂μ) + b * (tail + ∫ g, X g ∂μ) := by
      rw [integral_const_mul, integral_add (integrable_const _) hXi]
      simp
    _ ≤ a * tail + b * (tail + a * tail) :=
      add_le_add hXa (mul_le_mul_of_nonneg_left (add_le_add_left hXa tail) hb)
    _ = _ := by ring

end NLA.Proofs.RE06.GaussianMoment
