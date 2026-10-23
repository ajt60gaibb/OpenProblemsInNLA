import NLA.TR06.WeightedArea
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! The retained rectangular weighted area theorem on an actual open smooth
chart. Global measurability is supplied by a proved measurable extension. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.NormalizedGraphArea
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set Filter
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

theorem open_immersion_lintegral {U s : Set E} (hU : IsOpen U)
    (f : E → F) (hf : ContDiffOn ℝ 1 f U)
    (hs : MeasurableSet s) (hsub : s ⊆ U)
    (hinj : InjOn f U) (hfi : ∀ x ∈ U, Function.Injective (fderiv ℝ f x))
    (w : F → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ y in f '' s, w y ∂(Measure.euclideanHausdorffMeasure (Module.finrank ℝ E))) =
      ∫⁻ x in s, ENNReal.ofReal ((fderiv ℝ f x).toLinearMap.normDet) * w (f x) := by
  have hEmb := MeasurableEmbedding.subtype_coe hU.measurableSet
  have hfm : Measurable (U.domRestrict f) := hf.continuousOn.domRestrict.measurable
  obtain ⟨g,hgm,hEq⟩ := hEmb.exists_measurable_extend hfm (fun _ => ⟨0⟩)
  have hgf (x : E) (hx : x ∈ U) : g x = f x := congrFun hEq ⟨x,hx⟩
  have hderiv : ∀ x ∈ s, HasFDerivWithinAt g (fderiv ℝ f x) s x := by
    intro x hx
    have hlocal : g =ᶠ[𝓝 x] f := by
      filter_upwards [hU.mem_nhds (hsub hx)] with y hy using hgf y hy
    have hb := ((hf.contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt one_ne_zero).hasFDerivAt
    exact (hb.congr_of_eventuallyEq hlocal).hasFDerivWithinAt
  have hgi : InjOn g s := by
    intro x hx y hy hxy
    apply hinj (hsub hx) (hsub hy)
    rwa [hgf x (hsub hx),hgf y (hsub hy)] at hxy
  have hJac : ContinuousOn (fun x => ENNReal.ofReal ((fderiv ℝ f x).toLinearMap.normDet)) U :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (NLA.TR06.Area.continuous_normDet.comp_continuousOn
        (hf.continuousOn_fderiv_of_isOpen hU le_rfl))
  have harea := NLA.TR06.Area.immersion_lintegral hs hgm hderiv
    (fun x hx => hfi x (hsub hx)) hgi ((hJac.mono hsub).aemeasurable hs) w hw
  rw [Set.image_congr (fun x hx => hgf x (hsub hx))] at harea
  rw [harea]
  apply setLIntegral_congr_fun hs
  intro x hx
  simp only [hgf x (hsub hx)]

#assert_trust kernel open_immersion_lintegral
#print axioms open_immersion_lintegral
end NLA.Proofs.TR06.NormalizedGraphArea
