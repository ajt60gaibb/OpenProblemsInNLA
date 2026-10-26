import NLA.Proofs.TR14.UnitTransformation
import NLA.Proofs.TR14.UnitAvoidance
import NLA.Proofs.TR14.ContextualReduced

/-! The contextual product dimension inequality in TR-14 Section 4. Its only
finiteness input concerns reduced auxiliary subalgebras, and all those
auxiliaries are proved reduced from the exact Frobenius context. A finite
subspace avoidance argument replaces the manuscript's Vandermonde parameter
selection while preserving its actual mathematical assumptions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

variable {K A C : Type*} [Field K] [Infinite K] [CommRing A] [CommRing C]
  [Algebra K A] [Algebra K C] [IsReduced C] [FiniteDimensional K A]
  [FiniteDimensional K C]

/-- The actual one-step dimension inequality, assuming finiteness only of
reduced subalgebras. That finiteness must be established for the ambient
algebra at the eventual application. -/
theorem contextual_product_step_of_finite_reduced
    (hfinite : {S : Subalgebra K (A × C) | IsReduced S}.Finite)
    (Λ : (A × C) →ₗ[K] K) (U V Q W : Submodule K (A × C))
    (hU : (1 : A × C) ∈ U) (hV : (1 : A × C) ∈ V)
    (hFrob : ∀ a : A, (∀ b : A, Λ (a * b, 0) = 0) → a = 0)
    (hQ : ∀ b : A, ∃ x ∈ V * Q, x.1 = b)
    (hann : ∀ w ∈ W, Λ w = 0)
    (hUVQ : (U * V) * Q ≤ W) :
    Module.finrank K U + Module.finrank K V ≤
      Module.finrank K (U * V) + Module.finrank K (productStabilizer (U * V)) := by
  classical
  nontriviality A × C
  let I := {a : (A × C)ˣ // (a : A × C) ∈ U}
  choose S T hAV hTUV hST hdim using
    (fun a : I => linearTransformation_unit U V hV a.1 a.2)
  have hred (a : I) : IsReduced (S a) := by
    apply auxiliarySubalgebra_isReduced_of_context Λ V Q (T a) W
      hFrob hQ hann a.1 (a.1.isUnit.map (RingHom.fst A C)) (S a) (hST a)
    · intro v hv
      exact hAV a ((mem_unitScale a.1 V _).mpr ⟨v, hv, rfl⟩)
    · apply Submodule.mul_le.mpr
      intro t ht q hq
      exact hUVQ (Submodule.mul_mem_mul (hTUV a ht) hq)
  let J := {S : Subalgebra K (A × C) // IsReduced S}
  let : Finite J := hfinite.to_subtype
  let classes (j : J) : Set (A × C) :=
    {x | ∃ a : I, (a.1 : A × C) = x ∧ S a = j.1}
  have hclasses (j : J) (x : A × C) (hx : x ∈ classes j) : x ∈ U := by
    obtain ⟨a, rfl, _⟩ := hx
    exact a.2
  have hcover (x : A × C) (hx : x ∈ U) (hunit : IsUnit x) :
      ∃ j : J, x ∈ classes j := by
    obtain ⟨a, rfl⟩ := hunit
    exact ⟨⟨S ⟨a, hx⟩, hred ⟨a, hx⟩⟩, ⟨a, hx⟩, rfl, rfl⟩
  obtain ⟨j, hj⟩ := exists_unit_class_spans U hU classes hclasses hcover
  have hgen (z : A × C) (hz : z ∈ j.1) (u : A × C) (hu : u ∈ U)
      (v : A × C) (hv : v ∈ V) : z * (u * v) ∈ U * V := by
    have huspan : u ∈ Submodule.span K (classes j) := hj.symm ▸ hu
    refine Submodule.span_induction (fun x hx => ?_) (by simp)
      (fun x y _ _ hx hy => ?_) (fun c x _ hx => ?_) huspan
    · obtain ⟨a, rfl, hSa⟩ := hx
      have hzS : z ∈ S a := hSa.symm ▸ hz
      have hav : (a.1 : A × C) * v ∈ T a :=
        hAV a ((mem_unitScale a.1 V _).mpr ⟨v, hv, rfl⟩)
      exact hTUV a (hST a (Submodule.mul_mem_mul hzS hav))
    · simpa only [add_mul, mul_add] using (U * V).add_mem hx hy
    · simpa only [smul_mul_assoc, mul_smul_comm] using (U * V).smul_mem c hx
  have hjstab : j.1 ≤ productStabilizer (U * V) := by
    intro z hz w hw
    refine Submodule.mul_induction_on hw (fun u hu v hv => hgen z hz u hu v hv)
      (fun x y hx hy => ?_)
    simpa only [mul_add] using (U * V).add_mem hx hy
  have hn : (classes j).Nonempty := by
    by_contra hn
    have he : classes j = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hzero : U = ⊥ := by rw [← hj, he, Submodule.span_empty]
    have h10 : (1 : A × C) = 0 := by simpa only [hzero, Submodule.mem_bot] using hU
    exact one_ne_zero h10
  obtain ⟨x, a, hax, hSa⟩ := hn
  have hTd := Submodule.finrank_mono (hTUV a)
  have hjstab' : j.1.toSubmodule ≤ (productStabilizer (U * V)).toSubmodule := hjstab
  have hSd := Submodule.finrank_mono hjstab'
  change Module.finrank K j.1 ≤ Module.finrank K (productStabilizer (U * V)) at hSd
  have h := hdim a
  rw [hSa] at h
  omega

#assert_trust kernel contextual_product_step_of_finite_reduced
#print axioms contextual_product_step_of_finite_reduced

end NLA.Proofs.TR14
