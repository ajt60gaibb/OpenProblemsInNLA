import NLA.Proofs.TR14.UnitScaleProducts

/-! Unit scaling of products and stable spaces, used to undo the normalization
in the actual transformation lemma. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B]

open scoped Pointwise

/-- The explicit linear image agrees with Mathlib's pointwise multiplier. -/
theorem unitScale_eq_pointwise (u : Bˣ) (U : Submodule K B) :
    unitScale u U = (u : B) • U := rfl

theorem unitScale_mono (u : Bˣ) {U V : Submodule K B} (h : U ≤ V) :
    unitScale u U ≤ unitScale u V := Submodule.map_mono h

/-- Scaling either product factor scales the whole product. -/
theorem unitScale_mul_right (u : Bˣ) (U V : Submodule K B) :
    unitScale u (U * V) = unitScale u U * V := by
  simp only [unitScale_eq_pointwise, smul_mul_assoc]

/-- The same auxiliary algebra stabilizes a unit-scaled space. -/
theorem unitScale_stable (u : Bˣ) (S : Subalgebra K B) (T : Submodule K B)
    (hST : S.toSubmodule * T ≤ T) :
    S.toSubmodule * unitScale u T ≤ unitScale u T := by
  apply Submodule.mul_le.mpr
  intro z hz t ht
  obtain ⟨x, hx, hxt⟩ := (mem_unitScale u T t).mp ht
  apply (mem_unitScale u T _).mpr
  refine ⟨z * x, hST (Submodule.mul_mem_mul hz hx), ?_⟩
  rw [← hxt]
  ring

#assert_trust kernel unitScale_mul_right
#assert_trust kernel unitScale_stable
#print axioms unitScale_stable

end NLA.Proofs.TR14
