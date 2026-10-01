import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The isometric polar map on the actual absolute-value range

For a bounded operator `B`, the identity `abs B * abs B = B† * B`
shows that `abs B x` and `B x` have the same norm. Thus the map
`abs B x ↦ B x` is well defined and complex linear on the range of
`abs B`, and is an isometry there. No closed-range or injectivity
assumption is imposed. Extension to the range closure is a separate step.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The positive absolute value preserves the norm of each operator image. -/
theorem operatorAbs_apply_norm (B : H →L[ℂ] H) (x : H) :
    ‖CFC.abs B x‖ = ‖B x‖ := by
  have hprod : (CFC.abs B).adjoint.comp (CFC.abs B) = B.adjoint.comp B := by
    change star (CFC.abs B) * CFC.abs B = star B * B
    rw [(CFC.abs_nonneg B).star_eq, CFC.abs_mul_abs]
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left, hprod]

/-- Equality of kernels is the well-definedness condition for the polar map;
in particular, no injectivity of `B` is needed. -/
theorem operatorAbs_ker (B : H →L[ℂ] H) :
    LinearMap.ker (CFC.abs B).toLinearMap = LinearMap.ker B.toLinearMap := by
  ext x
  change CFC.abs B x = 0 ↔ B x = 0
  rw [← norm_eq_zero, operatorAbs_apply_norm, norm_eq_zero]

/-- The algebraic polar map on `range (abs B)`, defined by the common-kernel
quotient. The domain carries its inherited norm, whether or not it is closed. -/
def operatorPolarRangeMap (B : H →L[ℂ] H) :
    LinearMap.range (CFC.abs B).toLinearMap →ₗ[ℂ] H :=
  ((LinearMap.ker (CFC.abs B).toLinearMap).liftQ B.toLinearMap
    (le_of_eq (operatorAbs_ker B))).comp
      (CFC.abs B).toLinearMap.quotKerEquivRange.symm.toLinearMap

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem operatorPolarRangeMap_apply (B : H →L[ℂ] H) (x : H) :
    operatorPolarRangeMap B ⟨CFC.abs B x, ⟨x, rfl⟩⟩ = B x := by
  simp only [operatorPolarRangeMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [(CFC.abs B).toLinearMap.quotKerEquivRange_symm_apply_image x]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem operatorPolarRangeMap_norm (B : H →L[ℂ] H)
    (y : LinearMap.range (CFC.abs B).toLinearMap) :
    ‖operatorPolarRangeMap B y‖ = ‖y‖ := by
  obtain ⟨y, x, rfl⟩ := y
  exact (congrArg norm (operatorPolarRangeMap_apply B x)).trans
    (operatorAbs_apply_norm B x).symm

/-- The initial polar isometry. It is defined on the actual, possibly
nonclosed range of the positive absolute value. -/
def operatorPolarRangeIsometry (B : H →L[ℂ] H) :
    LinearMap.range (CFC.abs B).toLinearMap →ₗᵢ[ℂ] H where
  toLinearMap := operatorPolarRangeMap B
  norm_map' := operatorPolarRangeMap_norm B

@[simp]
theorem operatorPolarRangeIsometry_apply (B : H →L[ℂ] H) (x : H) :
    operatorPolarRangeIsometry B ⟨CFC.abs B x, ⟨x, rfl⟩⟩ = B x :=
  operatorPolarRangeMap_apply B x

/-- The initial polar isometry maps onto the actual range of `B`. -/
theorem operatorPolarRangeIsometry_range (B : H →L[ℂ] H) :
    LinearMap.range (operatorPolarRangeIsometry B).toLinearMap =
      LinearMap.range B.toLinearMap := by
  ext y
  constructor
  · rintro ⟨⟨z, x, rfl⟩, hy⟩
    exact ⟨x, (operatorPolarRangeIsometry_apply B x).symm.trans hy⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨CFC.abs B x, ⟨x, rfl⟩⟩, operatorPolarRangeIsometry_apply B x⟩

end ProofProject
