import NLA.Proofs.TR06.ControlledProjectionAtlas
import Mathlib.Analysis.Calculus.LineDeriv.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Topology NNReal
open Set Filter
namespace NLA.Proofs.TR06
open NLA.TR06.Area.Proposed

/-- A pointwise local norm comparison differentiates along actual real lines. -/
theorem fderiv_norm_le_of_local_comparison
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : E → G} {x : E} {C : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hnear : ∀ᶠ y in 𝓝 x, ‖f y - f x‖ ≤ C * ‖g y - g x‖) (v : E) :
    ‖fderiv ℝ f x v‖ ≤ C * ‖fderiv ℝ g x v‖ := by
  have hc0 : ContinuousAt (fun t : ℝ => x+t•v) 0 :=
    continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  have hc : Tendsto (fun t : ℝ => x+t•v) (𝓝[>] 0) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using hc0.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply le_of_tendsto_of_tendsto
    (hf.hasFDerivAt.hasLineDerivAt v |>.tendsto_slope_zero_right.norm)
    (tendsto_const_nhds.mul (hg.hasFDerivAt.hasLineDerivAt v |>.tendsto_slope_zero_right.norm))
  filter_upwards [hc.eventually hnear] with t ht
  simp only [norm_smul]
  calc
    ‖t⁻¹‖ * ‖f (x+t•v)-f x‖ ≤ ‖t⁻¹‖ * (C * ‖g (x+t•v)-g x‖) :=
      mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ = C * (‖t⁻¹‖ * ‖g (x+t•v)-g x‖) := by ring

/-- An actual open Lipschitz projection-inverse witness forces the genuine
selected projection derivative to be injective on every smooth chart tangent. -/
theorem controlled_projection_chart_derivative_injective {m N : ℕ}
    {K : ℝ≥0} {S : Set (Euclid N)} (σ : Fin m ↪ Fin N)
    (c : OpenPartialHomeomorph (Euclid m) S) (u : Euclid m) (hu : u ∈ c.source)
    (hsm : DifferentiableAt ℝ (fun v => (c v).val) u)
    (hinj : Function.Injective (fderiv ℝ (fun v => (c v).val) u))
    (hctl : (c u).val ∈ ControlledProjectionSet K S σ) :
    Function.Injective (fderiv ℝ (fun v => coordProjection σ (c v).val) u) := by
  obtain ⟨b,w,hw,hbw,hLip,hπ⟩ := hctl
  have hcu : c u ∈ b.target := by
    have heq : b w = c u := Subtype.ext hbw
    rw [← heq]
    exact b.map_source hw
  have hnear : ∀ᶠ v in 𝓝 u, c v ∈ b.target :=
    (c.continuousOn.continuousAt (c.open_source.mem_nhds hu)).preimage_mem_nhds
      (b.open_target.mem_nhds hcu)
  have hnorm : ∀ᶠ v in 𝓝 u, ‖(c v).val-(c u).val‖ ≤
      (K : ℝ) * ‖coordProjection σ (c v).val-coordProjection σ (c u).val‖ := by
    filter_upwards [hnear] with v hv
    have hv' := b.symm.map_source hv
    have hu' := b.symm.map_source hcu
    have H := hLip.norm_sub_le hv' hu'
    have hpv : coordProjection σ (c v).val = b.symm (c v) := by
      simpa only [b.right_inv hv] using hπ _ hv'
    have hpu : coordProjection σ (c u).val = b.symm (c u) := by
      simpa only [b.right_inv hcu] using hπ _ hu'
    simp only [b.right_inv hv,b.right_inv hcu] at H
    rwa [← hpv,← hpu] at H
  have hdiff : DifferentiableAt ℝ (fun v => coordProjection σ (c v).val) u :=
    (coordProjectionL σ).differentiableAt.comp u hsm
  intro v w h
  apply hinj
  apply sub_eq_zero.mp
  have H := fderiv_norm_le_of_local_comparison hsm hdiff hnorm (v-w)
  have hz : fderiv ℝ (fun v => coordProjection σ (c v).val) u (v-w) = 0 := by
    simpa only [map_sub,sub_eq_zero] using h
  rw [hz,norm_zero,mul_zero] at H
  simpa only [map_sub] using norm_eq_zero.mp (le_antisymm H (norm_nonneg _))

#assert_trust kernel fderiv_norm_le_of_local_comparison
#assert_trust kernel controlled_projection_chart_derivative_injective
#print axioms fderiv_norm_le_of_local_comparison
#print axioms controlled_projection_chart_derivative_injective
end NLA.Proofs.TR06
