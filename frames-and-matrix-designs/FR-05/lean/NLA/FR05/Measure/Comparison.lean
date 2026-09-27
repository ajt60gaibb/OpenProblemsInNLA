/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Integral

/-!
# Densities of mixtures and event-local Cauchy–Schwarz

This file depends only on mathlib, not on the phase-retrieval construction.

* `MeasureTheory.Measure.map_prod_eq_withDensity` identifies the density of a
  parametrised mixture. The parameter, source, and target spaces may differ;
  the density is extended-nonnegative-valued, so no integrability is required.
* `MeasureTheory.Measure.map_prod_eq_withDensity_ofReal` handles real densities.
* `MeasureTheory.Measure.pi_withDensity_ofReal` identifies finite product densities,
  requiring only integrability and nonnegativity of the individual density.
* `MeasureTheory.Measure.map_prod_eq_withDensity_of_inv` handles the inverse-action
  convention for an inversion-invariant parameter law (in particular Haar measure).
* `MeasureTheory.abs_setIntegral_le_sqrt_integral_sq` bounds an event integral
  using a global second moment and the measure of the event.
-/

set_option autoImplicit false

open scoped ENNReal

namespace MeasureTheory

section CauchySchwarz

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}

/-- Cauchy–Schwarz on a finite-measure set, using only the second moment on that set. -/
theorem abs_setIntegral_le_sqrt_setIntegral_sq (s : Set X) [IsFiniteMeasure (μ.restrict s)]
    (hf : MemLp f 2 (μ.restrict s)) :
    |∫ x in s, f x ∂μ| ≤ Real.sqrt ((∫ x in s, f x ^ 2 ∂μ) * μ.real s) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ.restrict s) Real.HolderConjugate.two_two
    (f := fun x ↦ ‖f x‖) (g := fun _ ↦ (1 : ℝ))
    (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
    (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
    (by simpa using hf.norm)
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : X ↦ (1 : ℝ)) 2 (μ.restrict s)))
  simp only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul,
    ← Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs, Measure.real_def,
    Measure.restrict_apply_univ] at h
  calc
    _ ≤ ∫ x in s, |f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ Real.sqrt (∫ x in s, f x ^ 2 ∂μ) * Real.sqrt (μ.real s) := h
    _ = _ := (Real.sqrt_mul (integral_nonneg fun x ↦ sq_nonneg (f x)) _).symm

/-- Event-local Cauchy–Schwarz with the global second moment. -/
theorem abs_setIntegral_le_sqrt_integral_sq [IsFiniteMeasure μ]
    (hf : MemLp f 2 μ) (s : Set X) :
    |∫ x in s, f x ∂μ| ≤ Real.sqrt ((∫ x, f x ^ 2 ∂μ) * μ.real s) := by
  grw [abs_setIntegral_le_sqrt_setIntegral_sq s (hf.restrict s),
    setIntegral_le_integral hf.integrable_sq
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg (f x))]

end CauchySchwarz

namespace Measure

/-- A finite independent product of density laws has the product density. -/
theorem pi_withDensity_ofReal {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (f : X → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f μ) :
    Measure.pi (fun _ : ι ↦ μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) =
      (Measure.pi (fun _ : ι ↦ μ)).withDensity
        (fun a ↦ ENNReal.ofReal (∏ i, f (a i))) := by
  have := isFiniteMeasure_withDensity_ofReal hfi.2
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    ← ofReal_integral_eq_lintegral_ofReal
      (Integrable.fintype_prod (fun i ↦ hfi.restrict))
      (Filter.Eventually.of_forall fun a ↦ Finset.prod_nonneg fun i _ ↦ hf0 (a i)),
    integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ integral_nonneg hf0)]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i),
    ofReal_integral_eq_lintegral_ofReal hfi.restrict (Filter.Eventually.of_forall hf0)]

section Mixture

variable {G X Y : Type*} [MeasurableSpace G] [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure G) (μ : Measure X) (ν : Measure Y) [SFinite ρ] [SFinite μ] [SFinite ν]

/-- A mixture of pushforward measures has the averaged density. No group structure,
normalisation, or integrability of the extended-nonnegative density is required. -/
theorem map_prod_eq_withDensity
    (T : G → Y → X) (hT : Measurable (Function.uncurry T))
    (d : G → X → ℝ≥0∞) (hd : Measurable (Function.uncurry d))
    (hmap : ∀ g, ν.map (T g) = μ.withDensity (d g)) :
    (ρ.prod ν).map (Function.uncurry T) = μ.withDensity (fun x ↦ ∫⁻ g, d g x ∂ρ) := by
  apply ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hT]
  simp only [Function.uncurry_def]
  rw [lintegral_prod (fun p : G × Y ↦ f (T p.1 p.2)) (hf.comp hT).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hd.lintegral_prod_left hf]
  calc
    _ = ∫⁻ g, ∫⁻ x, d g x * f x ∂μ ∂ρ := by
      apply lintegral_congr
      intro g
      rw [← lintegral_map hf (hT.of_uncurry_left (x := g)), hmap g]
      exact lintegral_withDensity_eq_lintegral_mul _ hd.of_uncurry_left hf
    _ = ∫⁻ x, ∫⁻ g, d g x * f x ∂ρ ∂μ :=
      lintegral_lintegral_swap (hd.mul (hf.comp measurable_snd)).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro x
      exact lintegral_mul_const _ (hd.of_uncurry_right (y := x))

/-- Real-valued form of `map_prod_eq_withDensity`, for nonnegative densities
integrable over the parameter space at each point. -/
theorem map_prod_eq_withDensity_ofReal
    (T : G → Y → X) (hT : Measurable (Function.uncurry T))
    (d : G → X → ℝ) (hd : Measurable (Function.uncurry d))
    (hd0 : ∀ g x, 0 ≤ d g x) (hdi : ∀ x, Integrable (fun g ↦ d g x) ρ)
    (hmap : ∀ g, ν.map (T g) = μ.withDensity (fun x ↦ ENNReal.ofReal (d g x))) :
    (ρ.prod ν).map (Function.uncurry T) =
      μ.withDensity (fun x ↦ ENNReal.ofReal (∫ g, d g x ∂ρ)) := by
  rw [map_prod_eq_withDensity ρ μ ν T hT (fun g x ↦ ENNReal.ofReal (d g x))
    hd.ennreal_ofReal hmap]
  congr 1
  funext x
  exact (ofReal_integral_eq_lintegral_ofReal (hdi x)
    (Filter.Eventually.of_forall fun g ↦ hd0 g x)).symm

/-- Inverse-action form of `map_prod_eq_withDensity_ofReal`. Only inversion
invariance of the parameter law is used, not the full Haar property. -/
theorem map_prod_eq_withDensity_of_inv [Group G] [MeasurableInv G] [ρ.IsInvInvariant]
    (T : G → Y → X) (hT : Measurable (Function.uncurry T))
    (d : G → X → ℝ) (hd : Measurable (Function.uncurry d))
    (hd0 : ∀ g x, 0 ≤ d g x) (hdi : ∀ x, Integrable (fun g ↦ d g x) ρ)
    (hmap : ∀ g, ν.map (T g⁻¹) = μ.withDensity (fun x ↦ ENNReal.ofReal (d g x))) :
    (ρ.prod ν).map (Function.uncurry T) =
      μ.withDensity (fun x ↦ ENNReal.ofReal (∫ g, d g x ∂ρ)) := by
  have h := map_prod_eq_withDensity_ofReal ρ μ ν T hT (fun g x ↦ d g⁻¹ x)
    (hd.comp (measurable_fst.inv.prodMk measurable_snd))
    (fun g x ↦ hd0 g⁻¹ x) (fun x ↦ (hdi x).comp_inv)
    (fun g ↦ by simpa only [inv_inv] using hmap g⁻¹)
  rw [h]
  congr 1
  funext x
  exact congrArg ENNReal.ofReal (integral_inv_eq_self (fun g ↦ d g x) ρ)

end Mixture

end Measure

end MeasureTheory

namespace NLA.FR05

/-- Compatibility name for the original FR-05 event bound. -/
alias abs_setIntegral_le_sqrt_second_moment := MeasureTheory.abs_setIntegral_le_sqrt_integral_sq

/-- Compatibility name for the original FR-05 mixture identity. -/
alias haar_mixture_eq_withDensity := MeasureTheory.Measure.map_prod_eq_withDensity_of_inv

end NLA.FR05
