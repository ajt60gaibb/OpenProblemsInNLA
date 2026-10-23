/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.RegularChartDefinitions
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Topology
open Set Filter
namespace NLA.TR06.Proposed

/-- A finite-dimensional C1 immersion is injective on a small open patch,
where its derivative stays injective. This asserts no openness of its image. -/
theorem exists_immersion_patch
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} (hf : ContDiff ℝ 1 f) {z : E}
    (hinj : Function.Injective (fderiv ℝ f z))
    {V : Set E} (hV : IsOpen V) (hzV : z ∈ V) :
    ∃ W : Set E, IsOpen W ∧ z ∈ W ∧ W ⊆ V ∧
      InjOn f W ∧ ∀ x ∈ W, Function.Injective (fderiv ℝ f x) := by
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  let g : E → E := fun x => L (f x)
  have hg : ContDiff ℝ 1 g := L.contDiff.comp hf
  have hLg : L.comp (fderiv ℝ f z) = (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) := by
    ext x
    exact hL x
  have hgderiv : HasFDerivAt g (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) z := by
    rw [← hLg]
    exact L.hasFDerivAt.comp z ((hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt)
  let e := hg.contDiffAt.toOpenPartialHomeomorph g hgderiv one_ne_zero
  have hze : z ∈ e.source := hg.contDiffAt.mem_toOpenPartialHomeomorph_source hgderiv one_ne_zero
  let D : Set E := {x | Function.Injective (fderiv ℝ f x)}
  have hD : IsOpen D := ContinuousLinearMap.isOpen_injective.preimage (hf.continuous_fderiv one_ne_zero)
  refine ⟨e.source ∩ V ∩ D, (e.open_source.inter hV).inter hD, ⟨⟨hze, hzV⟩, hinj⟩,
    fun x hx => hx.1.2, ?_, fun x hx => hx.2⟩
  intro x hx y hy hxy
  apply e.injOn hx.1.1 hy.1.1
  exact congrArg L hxy

#print axioms exists_immersion_patch
#assert_trust kernel exists_immersion_patch
end NLA.TR06.Proposed
