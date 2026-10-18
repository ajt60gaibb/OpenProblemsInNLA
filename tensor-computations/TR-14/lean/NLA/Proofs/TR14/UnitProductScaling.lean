import NLA.Proofs.TR14.UnitScaleAction
import Mathlib.Algebra.Algebra.Operations

/-! Actual finite product and algebra-projection identities for independently
unit-normalized graph spaces. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.TR14

variable {K B D : Type*} [Field K] [CommRing B] [Algebra K B]
  [CommRing D] [Algebra K D]

@[simp] theorem unitScale_top (u : Bˣ) : unitScale u (⊤ : Submodule K B) = ⊤ := by
  ext x
  constructor
  · intro _; exact Submodule.mem_top
  · intro _
    exact (mem_unitScale u ⊤ x).mpr
      ⟨((u⁻¹ : Bˣ) : B) * x, Submodule.mem_top, by simp [← mul_assoc]⟩

theorem unitScale_mul (u v : Bˣ) (U V : Submodule K B) :
    unitScale u U * unitScale v V = unitScale (u * v) (U * V) := by
  rw [← unitScale_mul_right]
  have h : U * unitScale v V = unitScale v (U * V) := by
    rw [mul_comm U, ← unitScale_mul_right, mul_comm V U]
  rw [h, unitScale_comp]

/-- Every mode may be normalized by its own chosen actual unit. -/
theorem unitScale_prod {ι : Type*} (s : Finset ι) (u : ι → Bˣ) (U : ι → Submodule K B) :
    (∏ i ∈ s, unitScale (u i) (U i)) =
      unitScale (∏ i ∈ s, u i) (∏ i ∈ s, U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, ih, unitScale_mul]

/-- Algebra homomorphisms carry these actual unit images to the corresponding
unit images of their projected subspaces. -/
theorem unitScale_map (f : B →ₐ[K] D) (u : Bˣ) (U : Submodule K B) :
    (unitScale u U).map f.toLinearMap =
      unitScale (Units.map f.toMonoidHom u) (U.map f.toLinearMap) := by
  ext z
  constructor
  · rintro ⟨x, hx, hxz⟩
    obtain ⟨y, hy, hyx⟩ := (mem_unitScale u U x).mp hx
    apply (mem_unitScale _ _ z).mpr
    refine ⟨f y, ⟨y, hy, rfl⟩, ?_⟩
    change f (u : B) * f y = z
    rw [← map_mul, hyx]
    exact hxz
  · intro hz
    obtain ⟨y, ⟨x, hx, hxy⟩, hyz⟩ := (mem_unitScale _ _ z).mp hz
    apply Submodule.mem_map.mpr
    refine ⟨(u : B) * x, (mem_unitScale u U _).mpr ⟨x, hx, rfl⟩, ?_⟩
    change f x = y at hxy
    change f (u : B) * y = z at hyz
    change f ((u : B) * x) = z
    rw [map_mul, hxy]
    exact hyz

/-- Surjectivity of an actual projected subspace is preserved by normalization. -/
theorem unitScale_map_top (f : B →ₐ[K] D) (u : Bˣ) (U : Submodule K B)
    (hU : U.map f.toLinearMap = ⊤) :
    (unitScale u U).map f.toLinearMap = ⊤ := by
  rw [unitScale_map, hU, unitScale_top]

#assert_trust kernel unitScale_prod
#assert_trust kernel unitScale_map_top
#print axioms unitScale_map_top

end NLA.Proofs.TR14
