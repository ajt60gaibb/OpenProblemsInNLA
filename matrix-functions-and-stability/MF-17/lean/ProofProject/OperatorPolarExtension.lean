import ProofProject.OperatorPolarRange
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The polar operator on the whole Hilbert space

The isometry `abs B x ↦ B x` extends by continuity to the closure of
`range (abs B)`. Precomposing this extension with the orthogonal projection
onto that closed subspace gives a bounded operator `U` on the whole space.
Its initial support is precisely that orthogonal projection, and
`U * abs B = B`. The construction includes nonclosed ranges and zero spaces.
-/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closed initial space of the polar operator. -/
abbrev operatorPolarInitialSpace (B : H →L[ℂ] H) : Submodule ℂ H :=
  (LinearMap.range (CFC.abs B).toLinearMap).topologicalClosure

/-- Inclusion of the actual absolute-value range into its closure. -/
def operatorPolarRangeInclusion (B : H →L[ℂ] H) :
    LinearMap.range (CFC.abs B).toLinearMap →ₗ[ℂ] operatorPolarInitialSpace B :=
  Submodule.inclusion (LinearMap.range (CFC.abs B).toLinearMap).le_topologicalClosure

theorem operatorPolarRangeInclusion_dense (B : H →L[ℂ] H) :
    DenseRange (operatorPolarRangeInclusion B) := by
  exact (denseRange_inclusion_iff
    (show (LinearMap.range (CFC.abs B).toLinearMap : Set H) ⊆
      (operatorPolarInitialSpace B : Set H) from
      (LinearMap.range (CFC.abs B).toLinearMap).le_topologicalClosure)).mpr
        Set.Subset.rfl

/-- Continuous extension of the initial range isometry to the closed range. -/
def operatorPolarClosureMap (B : H →L[ℂ] H) : operatorPolarInitialSpace B →L[ℂ] H :=
  (operatorPolarRangeMap B).extendOfNorm (operatorPolarRangeInclusion B)

@[simp]
theorem operatorPolarClosureMap_inclusion (B : H →L[ℂ] H)
    (x : LinearMap.range (CFC.abs B).toLinearMap) :
    operatorPolarClosureMap B (operatorPolarRangeInclusion B x) =
      operatorPolarRangeMap B x := by
  apply LinearMap.extendOfNorm_eq (operatorPolarRangeInclusion_dense B)
  refine ⟨1, ?_⟩
  intro y
  rw [operatorPolarRangeMap_norm, one_mul]
  exact le_rfl

/-- Density preserves the exact norm identity, not only contractivity. -/
theorem operatorPolarClosureMap_norm (B : H →L[ℂ] H)
    (x : operatorPolarInitialSpace B) : ‖operatorPolarClosureMap B x‖ = ‖x‖ := by
  refine (operatorPolarRangeInclusion_dense B).induction_on
    (p := fun y => ‖operatorPolarClosureMap B y‖ = ‖y‖) x
    (isClosed_eq (operatorPolarClosureMap B).continuous.norm continuous_norm) ?_
  intro y
  rw [operatorPolarClosureMap_inclusion, operatorPolarRangeMap_norm]
  rfl

/-- The whole-space polar operator, zero on the orthogonal complement of
the closed absolute-value range. -/
def operatorPolar (B : H →L[ℂ] H) : H →L[ℂ] H :=
  (operatorPolarClosureMap B).comp (operatorPolarInitialSpace B).orthogonalProjectionOnto

@[simp]
theorem operatorPolar_apply_abs (B : H →L[ℂ] H) (x : H) :
    operatorPolar B (CFC.abs B x) = B x := by
  have hproj : (operatorPolarInitialSpace B).orthogonalProjectionOnto (CFC.abs B x) =
      operatorPolarRangeInclusion B ⟨CFC.abs B x, ⟨x, rfl⟩⟩ := by
    exact (operatorPolarInitialSpace B).orthogonalProjectionOnto_mem_subspace_eq_self
      (operatorPolarRangeInclusion B ⟨CFC.abs B x, ⟨x, rfl⟩⟩)
  change operatorPolarClosureMap B
    ((operatorPolarInitialSpace B).orthogonalProjectionOnto (CFC.abs B x)) = B x
  rw [hproj, operatorPolarClosureMap_inclusion, operatorPolarRangeMap_apply]

theorem operatorPolar_mul_abs (B : H →L[ℂ] H) :
    operatorPolar B * CFC.abs B = B := by
  ext x
  exact operatorPolar_apply_abs B x

/-- The extended isometry has identity Gram operator on its complete domain. -/
theorem operatorPolarClosureMap_adjoint_comp_self (B : H →L[ℂ] H) :
    (operatorPolarClosureMap B).adjoint.comp (operatorPolarClosureMap B) = 1 :=
  (operatorPolarClosureMap B).norm_map_iff_adjoint_comp_self.mp
    (operatorPolarClosureMap_norm B)

/-- The initial support of the polar operator is exactly the projection onto
the closed absolute-value range. -/
theorem operatorPolar_star_mul_self (B : H →L[ℂ] H) :
    star (operatorPolar B) * operatorPolar B = (operatorPolarInitialSpace B).starProjection := by
  change ((operatorPolarClosureMap B).comp
      (operatorPolarInitialSpace B).orthogonalProjectionOnto).adjoint.comp
    ((operatorPolarClosureMap B).comp (operatorPolarInitialSpace B).orthogonalProjectionOnto) =
      (operatorPolarInitialSpace B).subtypeL.comp
        (operatorPolarInitialSpace B).orthogonalProjectionOnto
  rw [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_orthogonalProjectionOnto,
    ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc (operatorPolarClosureMap B).adjoint
      (operatorPolarClosureMap B),
    operatorPolarClosureMap_adjoint_comp_self, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp]

/-- The support identity required by the balanced-factor construction. -/
theorem operatorPolar_support_abs (B : H →L[ℂ] H) :
    star (operatorPolar B) * operatorPolar B * CFC.abs B = CFC.abs B := by
  rw [operatorPolar_star_mul_self]
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  exact (LinearMap.range (CFC.abs B).toLinearMap).le_topologicalClosure ⟨x, rfl⟩

/-- The whole-space polar operator is a contraction, including the zero space. -/
theorem operatorPolar_norm_le (B : H →L[ℂ] H) : ‖operatorPolar B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖operatorPolarClosureMap B
    ((operatorPolarInitialSpace B).orthogonalProjectionOnto x)‖ ≤ 1 * ‖x‖
  rw [operatorPolarClosureMap_norm, one_mul]
  exact (operatorPolarInitialSpace B).norm_orthogonalProjectionOnto_apply_le x

end ProofProject
