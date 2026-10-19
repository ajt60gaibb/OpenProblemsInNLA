import NLA.Proofs.TR14.ProductStabilizer
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Unit changes of actual product spaces, and the dimension-preserving
intersection/sum transformation used in TR-14 Section 4. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B]

@[simp] theorem unitScale_one (U : Submodule K B) : unitScale (1 : Bˣ) U = U := by
  ext x
  simp only [mem_unitScale, Units.val_one, one_mul, exists_eq_right]

@[simp] theorem unitScale_comp (u v : Bˣ) (U : Submodule K B) :
    unitScale u (unitScale v U) = unitScale (u * v) U := by
  ext x
  rw [mem_unitScale, mem_unitScale]
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨z, hz, hzy⟩ := (mem_unitScale v U y).mp hy
    exact ⟨z, hz, by rw [Units.val_mul, mul_assoc, hzy, hyx]⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨(v : B) * z, (mem_unitScale v U _).mpr ⟨z, hz, rfl⟩,
      by rw [← mul_assoc, ← Units.val_mul, hzx]⟩

@[simp] theorem unitScale_inv_scale (u : Bˣ) (U : Submodule K B) :
    unitScale u⁻¹ (unitScale u U) = U := by simp

@[simp] theorem unitScale_scale_inv (u : Bˣ) (U : Submodule K B) :
    unitScale u (unitScale u⁻¹ U) = U := by simp

@[simp] theorem unitScale_inf (u : Bˣ) (U V : Submodule K B) :
    unitScale u (U ⊓ V) = unitScale u U ⊓ unitScale u V :=
  Submodule.map_inf _ (unitMultiplication u).injective

/-- Membership in the inverse image of a unit multiplier. -/
theorem mem_unitScale_inv_iff (u : Bˣ) (U : Submodule K B) (x : B) :
    x ∈ unitScale u⁻¹ U ↔ (u : B) * x ∈ U := by
  rw [mem_unitScale]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [← mul_assoc, Units.mul_inv, one_mul] using hy
  · intro hx
    exact ⟨(u : B) * x, hx, by simp [← mul_assoc]⟩

/-- The source intersection/sum transformation preserves the dimension sum. -/
theorem transformation_dimension_sum [FiniteDimensional K B]
    (u : Bˣ) (U V : Submodule K B) :
    Module.finrank K ↥(U ⊓ unitScale u⁻¹ V) +
      Module.finrank K ↥(V ⊔ unitScale u U) =
        Module.finrank K U + Module.finrank K V := by
  have hi : unitScale u (U ⊓ unitScale u⁻¹ V) = unitScale u U ⊓ V := by simp
  have hd := Submodule.finrank_sup_add_finrank_inf_eq V (unitScale u U)
  have hi' : unitScale u (U ⊓ unitScale u⁻¹ V) = V ⊓ unitScale u U :=
    hi.trans (inf_comm _ _)
  rw [← hi', finrank_unitScale, finrank_unitScale] at hd
  omega

/-- The actual transformed products stay inside the original product span. -/
theorem transformation_product_le (u : Bˣ) (U V : Submodule K B) :
    (U ⊓ unitScale u⁻¹ V) * (V ⊔ unitScale u U) ≤ U * V := by
  apply Submodule.mul_le.mpr
  intro x hx y hy
  have hxV : (u : B) * x ∈ V := (mem_unitScale_inv_iff u V x).mp hx.2
  obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  rw [mul_add]
  apply (U * V).add_mem (Submodule.mul_mem_mul hx.1 hv)
  obtain ⟨b, hb, hbeq⟩ := (mem_unitScale u U z).mp hz
  rw [← hbeq]
  have hmem : b * ((u : B) * x) ∈ U * V := Submodule.mul_mem_mul hb hxV
  convert hmem using 1; ring

#assert_trust kernel transformation_dimension_sum
#assert_trust kernel transformation_product_le
#print axioms transformation_product_le

end NLA.Proofs.TR14
