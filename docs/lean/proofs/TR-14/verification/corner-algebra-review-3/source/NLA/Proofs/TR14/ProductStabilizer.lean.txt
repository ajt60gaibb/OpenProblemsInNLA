import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Dimension.Finrank
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! Actual subspace products and their multiplicative stabilizer for the
ordinary lower-bound argument in TR-14, solution.tex Section 4. The product is
Mathlib's span of products. No product dimension inequality is assumed here. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B]

/-- The unital algebra of multipliers preserving an actual subspace. -/
def productStabilizer (W : Submodule K B) : Subalgebra K B where
  carrier := {a | ∀ w ∈ W, a * w ∈ W}
  zero_mem' := by intro w hw; simp
  add_mem' := by
    intro a b ha hb w hw
    simpa only [add_mul] using W.add_mem (ha w hw) (hb w hw)
  one_mem' := by intro w hw; simpa using hw
  mul_mem' := by
    intro a b ha hb w hw
    simpa only [mul_assoc] using ha (b * w) (hb w hw)
  algebraMap_mem' := by
    intro r w hw
    simpa only [Algebra.smul_def] using W.smul_mem r hw

@[simp] theorem mem_productStabilizer (W : Submodule K B) (a : B) :
    a ∈ productStabilizer W ↔ ∀ w ∈ W, a * w ∈ W := Iff.rfl

/-- Stabilizing multipliers acting on `W` span exactly `W`. -/
theorem productStabilizer_mul (W : Submodule K B) :
    (productStabilizer W).toSubmodule * W = W := by
  apply le_antisymm
  · exact Submodule.mul_le.mpr fun a ha w hw => ha w hw
  · intro w hw
    simpa only [one_mul] using
      Submodule.mul_mem_mul (show (1 : B) ∈ (productStabilizer W).toSubmodule from
        (productStabilizer W).one_mem) hw

/-- A stabilizer continues to act after taking a further product. -/
theorem productStabilizer_le_mul_right (U V : Submodule K B) :
    productStabilizer U ≤ productStabilizer (U * V) := by
  intro a ha w hw
  refine Submodule.mul_induction_on hw (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · simpa only [mul_assoc] using Submodule.mul_mem_mul (ha x hx) hy
  · simpa only [mul_add] using (U * V).add_mem hx hy

/-- Scalars always preserve any subspace. -/
theorem scalar_subalgebra_le_productStabilizer (W : Submodule K B) :
    (⊥ : Subalgebra K B) ≤ productStabilizer W := bot_le

/-- Adding product factors on either side preserves the stabilizing action. -/
theorem productStabilizer_le_mul_left (U V : Submodule K B) :
    productStabilizer V ≤ productStabilizer (U * V) := by
  simpa only [mul_comm U V] using productStabilizer_le_mul_right V U

/-- Multiplication by an actual unit is an invertible linear change. -/
def unitMultiplication (u : Bˣ) : B ≃ₗ[K] B where
  toFun x := (u : B) * x
  invFun x := ((u⁻¹ : Bˣ) : B) * x
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]
  map_add' x y := mul_add _ _ _
  map_smul' r x := by simp only [RingHom.id_apply, mul_smul_comm]

/-- The actual image subspace under multiplication by a unit. -/
def unitScale (u : Bˣ) (U : Submodule K B) : Submodule K B :=
  U.map (unitMultiplication u).toLinearMap

@[simp] theorem mem_unitScale (u : Bˣ) (U : Submodule K B) (x : B) :
    x ∈ unitScale u U ↔ ∃ y ∈ U, (u : B) * y = x := Iff.rfl

/-- Unit scaling preserves the actual finite dimension. -/
@[simp] theorem finrank_unitScale (u : Bˣ) (U : Submodule K B) :
    Module.finrank K (unitScale u U) = Module.finrank K U :=
  (unitMultiplication u).finrank_map_eq U

/-- A chosen unit in a mode becomes one after inverse scaling. -/
theorem one_mem_unitScale_inv (u : Bˣ) (U : Submodule K B) (hu : (u : B) ∈ U) :
    (1 : B) ∈ unitScale u⁻¹ U := by
  exact ⟨u, hu, by change ((u⁻¹ : Bˣ) : B) * (u : B) = 1; simp⟩

/-- A subspace containing one survives multiplication by another such space. -/
theorem submodule_le_mul_of_one_mem_right (U V : Submodule K B)
    (hV : (1 : B) ∈ V) : U ≤ U * V := by
  intro x hx
  simpa only [mul_one] using Submodule.mul_mem_mul hx hV

theorem submodule_le_mul_of_one_mem_left (U V : Submodule K B)
    (hU : (1 : B) ∈ U) : V ≤ U * V := by
  intro x hx
  simpa only [one_mul] using Submodule.mul_mem_mul hU hx

/-- Stabilizer control passes from a product prefix to any final tail. -/
theorem productStabilizer_le_list_tail (U : Submodule K B)
    (tail : List (Submodule K B)) :
    productStabilizer U ≤ productStabilizer (U * tail.prod) :=
  productStabilizer_le_mul_right U tail.prod

#assert_trust kernel productStabilizer_mul
#assert_trust kernel productStabilizer_le_mul_right
#assert_trust kernel finrank_unitScale
#print axioms productStabilizer_le_mul_right
#print axioms finrank_unitScale

end NLA.Proofs.TR14
