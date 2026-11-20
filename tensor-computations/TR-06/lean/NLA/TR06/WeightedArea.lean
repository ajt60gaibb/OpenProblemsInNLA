/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, George Stepaniants

Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology. Original TR-06 proof: Matthew J. Colbrook.
The pushforward argument follows Mathlib.MeasureTheory.Function.Jacobian,
with the previously proved rectangular immersion area formula.
-/
import NLA.TR06.Area
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory
open MeasureTheory Set
namespace NLA.TR06.Area

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {s : Set E} {f : E → F} {f' : E → E →L[ℝ] F}

local notation "ν" => (μHE[Module.finrank ℝ E] : Measure F)
local notation "μ" => (volume : Measure E)

/-- Push forward the exact rectangular Jacobian density. No measurability of
the chosen derivatives or finite-volume hypothesis is needed for this identity. -/
theorem immersion_map_withDensity (hs : MeasurableSet s) (hf : Measurable f)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hfi : ∀ x ∈ s, Function.Injective (f' x)) (hinj : Set.InjOn f s) :
    Measure.map f (((μ).restrict s).withDensity
      (fun x => ENNReal.ofReal (f' x).toLinearMap.normDet)) = (ν).restrict (f '' s) := by
  apply Measure.ext
  intro t ht
  rw [Measure.map_apply hf ht, withDensity_apply _ (hf ht),
    Measure.restrict_restrict (hf ht), Measure.restrict_apply ht]
  rw [← immersion_area ((hf ht).inter hs)
    (fun x hx => (hf' x hx.2).mono inter_subset_right)
    (fun x hx => hfi x hx.2) (hinj.mono inter_subset_right)]
  rw [Set.image_preimage_inter]

/-- Weighted area for a measurable weight and an a.e. measurable rectangular
Jacobian. Actual chart applications must establish these intermediate premises. -/
theorem immersion_lintegral (hs : MeasurableSet s) (hf : Measurable f)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hfi : ∀ x ∈ s, Function.Injective (f' x)) (hinj : Set.InjOn f s)
    (hj : AEMeasurable (fun x => ENNReal.ofReal (f' x).toLinearMap.normDet) ((μ).restrict s))
    (w : F → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ y in f '' s, w y ∂ν) =
      ∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet * w (f x) ∂μ := by
  rw [← immersion_map_withDensity hs hf hf' hfi hinj,
    lintegral_map hw hf]
  exact lintegral_withDensity_eq_lintegral_mul₀ hj (hw.comp hf).aemeasurable

#print axioms immersion_map_withDensity
#print axioms immersion_lintegral
#assert_trust kernel immersion_map_withDensity
#assert_trust kernel immersion_lintegral
end NLA.TR06.Area
