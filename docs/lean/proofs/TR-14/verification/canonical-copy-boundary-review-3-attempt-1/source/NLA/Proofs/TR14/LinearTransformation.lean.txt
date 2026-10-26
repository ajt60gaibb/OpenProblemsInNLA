import NLA.Proofs.TR14.UnitSpan
import NLA.Proofs.TR14.UnitScaleProducts

/-! The actual dimension induction for the commutative finite-dimensional
transformation lemma, TR-14 solution.tex Section 4, following the argument of
Beck--Lecouvey Lemma 4.2. The theorem below constructs the auxiliary subalgebra
and space; it does not assume a product-space dimension inequality. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

variable {K B : Type*} [Field K] [Infinite K] [CommRing B] [Algebra K B]
  [FiniteDimensional K B]

/-- To stabilize a one-containing subspace it suffices to preserve its units. -/
theorem le_productStabilizer_of_unit_products
    (U V : Submodule K B) (hV : (1 : B) ∈ V)
    (hunit : ∀ e : Bˣ, (e : B) ∈ V → ∀ x ∈ U, x * (e : B) ∈ V) :
    U ≤ (productStabilizer V).toSubmodule := by
  intro x hx v hv
  have hvspan : v ∈ Submodule.span K {y : B | y ∈ V ∧ IsUnit y} := by
    simpa only [span_units_eq_of_one_mem V hV] using hv
  refine Submodule.span_induction (fun y hy => ?_) (by simp)
    (fun y z _ _ hy hz => ?_) (fun c y _ hy => ?_) hvspan
  · obtain ⟨e, he⟩ := hy.2
    exact he ▸ hunit e (he.symm ▸ hy.1) x hx
  · simpa only [mul_add] using V.add_mem hy hz
  · simpa only [mul_smul_comm] using V.smul_mem c hy

/-- Normalized transformation lemma: an actual auxiliary `S,T` exists, with
`V≤T≤UV`, `S*T≤T`, and the required sum-of-dimensions inequality. -/
theorem linearTransformation_normalized (U V : Submodule K B)
    (hU : (1 : B) ∈ U) (hV : (1 : B) ∈ V) :
    ∃ S : Subalgebra K B, ∃ T : Submodule K B,
      V ≤ T ∧ T ≤ U * V ∧ S.toSubmodule * T ≤ T ∧
        Module.finrank K U + Module.finrank K V ≤
          Module.finrank K T + Module.finrank K S := by
  classical
  induction hd : Module.finrank K U using Nat.strong_induction_on generalizing U V with
  | h d ih =>
    by_cases hs : ∀ e : Bˣ, (e : B) ∈ V → ∀ x ∈ U, x * (e : B) ∈ V
    · have hUS := le_productStabilizer_of_unit_products U V hV hs
      refine ⟨productStabilizer V, V, le_rfl,
        submodule_le_mul_of_one_mem_left U V hU, ?_, ?_⟩
      · exact le_of_eq (productStabilizer_mul V)
      · have hdim := Submodule.finrank_mono hUS
        change Module.finrank K U ≤ Module.finrank K (productStabilizer V) at hdim
        omega
    · push Not at hs
      obtain ⟨e, heV, x, hxU, hxV⟩ := hs
      let Ue : Submodule K B := U ⊓ unitScale e⁻¹ V
      let Ve : Submodule K B := V ⊔ unitScale e U
      have hUe1 : (1 : B) ∈ Ue := by
        exact ⟨hU, (mem_unitScale_inv_iff e V 1).mpr (by simpa using heV)⟩
      have hVe1 : (1 : B) ∈ Ve := Submodule.mem_sup_left hV
      have hlt : Ue < U := by
        apply lt_of_le_of_ne inf_le_left
        intro heq
        have hxUe : x ∈ Ue := by
          change x ∈ U ⊓ unitScale e⁻¹ V
          rw [heq]
          exact hxU
        have hxe : (e : B) * x ∈ V := (mem_unitScale_inv_iff e V x).mp hxUe.2
        exact hxV (by simpa only [mul_comm] using hxe)
      have hdimlt : Module.finrank K Ue < d := by
        rw [← hd]
        exact Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨S, T, hVeT, hTprod, hST, hdim⟩ :=
        ih (Module.finrank K Ue) hdimlt Ue Ve hUe1 hVe1 rfl
      refine ⟨S, T, le_trans le_sup_left hVeT,
        hTprod.trans (transformation_product_le e U V), hST, ?_⟩
      have hsum := transformation_dimension_sum e U V
      change Module.finrank K Ue + Module.finrank K Ve =
        Module.finrank K U + Module.finrank K V at hsum
      omega

#assert_trust kernel le_productStabilizer_of_unit_products
#assert_trust kernel linearTransformation_normalized
#print axioms linearTransformation_normalized

end NLA.Proofs.TR14
