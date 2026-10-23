import NLA.Proofs.TR14.CornerStabilizer
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Actual inherited list context and primitive block dimension inequalities.
The block lower mode dimensions remain explicit inputs supplied by the actual
quotient polynomial-image construction. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

noncomputable section
variable {A C : Type*} [CommRing A] [CommRing C] [Algebra ℂ A] [Algebra ℂ C]

/-- Every actual all-but-one first projection descends to the first corner. -/
theorem cornerBlock_list_allbutone_projection (e : A × C)
    (L : List (Submodule ℂ (A × C)))
    (hproj : ∀ i < L.length, ∀ b : A,
      ∃ x ∈ (L.take i).prod * (L.drop (i + 1)).prod, x.1 = b) :
    ∀ i < (L.map (cornerBlockSpace (K := ℂ) e)).length,
      ∀ b : IdempotentCorner e.1,
      ∃ x ∈ ((L.map (cornerBlockSpace (K := ℂ) e)).take i).prod *
        ((L.map (cornerBlockSpace (K := ℂ) e)).drop (i + 1)).prod, x.1 = b := by
  intro i hi b
  have hi' : i < L.length := by simpa using hi
  obtain ⟨x, hx, hxb⟩ := cornerBlockSpace_fst_surjective e
    ((L.take i).prod * (L.drop (i + 1)).prod) (hproj i hi') b
  refine ⟨x, ?_, hxb⟩
  rw [← List.map_take, ← List.map_drop, cornerBlockSpace_list_prod,
    cornerBlockSpace_list_prod]
  change x ∈ ((L.take i).prod.map (cornerBlockProjection (K := ℂ) e).toLinearMap) *
    ((L.drop (i + 1)).prod.map (cornerBlockProjection (K := ℂ) e).toLinearMap)
  rw [← Submodule.map_mul]
  exact hx

/-- The block functional is nonzero when its actual first idempotent
component is nonzero, by the original Frobenius nondegeneracy. -/
theorem cornerBlockFunctional_ne_zero (e : A × C) (he : e * e = e)
    (Λ : (A × C) →ₗ[ℂ] ℂ)
    (hFrob : ∀ a : A, (∀ b : A, Λ (a * b, 0) = 0) → a = 0)
    (heA : e.1 ≠ 0) : cornerBlockFunctional e he Λ ≠ 0 := by
  intro hz
  apply heA
  apply hFrob
  intro b
  have h := DFunLike.congr_fun hz (cornerProjection (K := ℂ) e.1 b, 0)
  simp only [cornerBlockFunctional, LinearMap.comp_apply, cornerBlockInclusion,
    LinearMap.prodMap_apply, cornerInclusion_projection, map_zero, LinearMap.zero_apply] at h
  exact h

variable [FiniteDimensional ℂ A] [FiniteDimensional ℂ C]

/-- The contextual dimension bound inside the actual primitive block,
with its intrinsic stabilizer proved scalar by actual primitive action. -/
theorem primitive_corner_list_dimension_bound [IsReduced C]
    (Λ : (A × C) →ₗ[ℂ] ℂ) (L : List (Submodule ℂ (A × C)))
    (hne : L ≠ []) (hone : ∀ U ∈ L, (1 : A × C) ∈ U)
    (hFrob : ∀ a : A, (∀ b : A, Λ (a * b, 0) = 0) → a = 0)
    (hann : ∀ w ∈ L.prod, Λ w = 0)
    (hproj : ∀ i < L.length, ∀ b : A,
      ∃ x ∈ (L.take i).prod * (L.drop (i + 1)).prod, x.1 = b)
    {t : ℕ} (φ : productStabilizer L.prod ≃ₐ[ℂ] (Fin t → ℂ)) (j : Fin t) :
    ((L.map (cornerBlockSpace (K := ℂ) (reducedBlockIdempotent (productStabilizer L.prod) φ j))).map
      (fun U : Submodule ℂ
        (IdempotentCorner (reducedBlockIdempotent (productStabilizer L.prod) φ j).1 ×
         IdempotentCorner (reducedBlockIdempotent (productStabilizer L.prod) φ j).2) =>
          Module.finrank ℂ U)).sum ≤
      Module.finrank ℂ (cornerBlockSpace (K := ℂ)
        (reducedBlockIdempotent (productStabilizer L.prod) φ j) L.prod) + (L.length - 1) := by
  let e := reducedBlockIdempotent (productStabilizer L.prod) φ j
  have he : e * e = e := reducedBlockIdempotent_mul_self (productStabilizer L.prod) φ j
  have heW : e ∈ productStabilizer L.prod := reducedBlockIdempotent_mem (productStabilizer L.prod) φ j
  let : IsReduced (IdempotentCorner e.2) := corner_isReduced (K := ℂ) e.2 (congrArg Prod.snd he)
  have hblockann : ∀ w ∈ (L.map (cornerBlockSpace (K := ℂ) e)).prod,
      cornerBlockFunctional e he Λ w = 0 := by
    rw [cornerBlockSpace_list_prod]
    exact cornerBlockSpace_annihilated e he Λ L.prod heW hann
  have hstab : Module.finrank ℂ (productStabilizer
      (L.map (cornerBlockSpace (K := ℂ) e)).prod) ≤ 1 := by
    rw [cornerBlockSpace_list_prod]
    exact primitive_corner_stabilizer_finrank_le_one L.prod φ j
  have h := contextual_product_list_dimension_bound_of_stabilizer_finrank_le_one
    (cornerBlockFunctional e he Λ) (L.map (cornerBlockSpace (K := ℂ) e))
    (by simpa using hne) (by
      intro U hU
      obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hU
      exact one_mem_cornerBlockSpace e V (hone V hV))
    (cornerBlockFunctional_frobenius e he Λ hFrob) hblockann
    (cornerBlock_list_allbutone_projection e L hproj) hstab
  have heqdim := congrArg (fun U : Submodule ℂ
    (IdempotentCorner e.1 × IdempotentCorner e.2) => Module.finrank ℂ U)
      (cornerBlockSpace_list_prod (K := ℂ) e L)
  rw [heqdim] at h
  simpa only [List.length_map] using h

/-- Actual annihilation by a nonzero block functional supplies codimension
at least one in the intrinsic product corner. -/
theorem cornerBlockSpace_finrank_upper
    (e : A × C) (he : e * e = e) (Λ : (A × C) →ₗ[ℂ] ℂ)
    (W : Submodule ℂ (A × C)) (heW : e ∈ productStabilizer W)
    (hFrob : ∀ a : A, (∀ b : A, Λ (a * b, 0) = 0) → a = 0)
    (hann : ∀ w ∈ W, Λ w = 0) (heA : e.1 ≠ 0) :
    Module.finrank ℂ (cornerBlockSpace (K := ℂ) e W) + 1 ≤
      Module.finrank ℂ (IdempotentCorner e.1) + Module.finrank ℂ (IdempotentCorner e.2) := by
  have hle : cornerBlockSpace (K := ℂ) e W ≤ LinearMap.ker (cornerBlockFunctional e he Λ) :=
    cornerBlockSpace_annihilated e he Λ W heW hann
  have hd := Submodule.finrank_mono hle
  have hr := Module.Dual.finrank_ker_add_one_of_ne_zero
    (cornerBlockFunctional_ne_zero e he Λ hFrob heA)
  rw [Module.finrank_prod] at hr
  omega

/-- The actual primitive block inequality in additive natural-number form.
Only the independently proved actual mode dimension lower bound is supplied. -/
theorem primitive_corner_block_dimension_inequality [IsReduced C]
    (Λ : (A × C) →ₗ[ℂ] ℂ) (L : List (Submodule ℂ (A × C)))
    (hne : L ≠ []) (hone : ∀ U ∈ L, (1 : A × C) ∈ U)
    (hFrob : ∀ a : A, (∀ b : A, Λ (a * b, 0) = 0) → a = 0)
    (hann : ∀ w ∈ L.prod, Λ w = 0)
    (hproj : ∀ i < L.length, ∀ b : A,
      ∃ x ∈ (L.take i).prod * (L.drop (i + 1)).prod, x.1 = b)
    {t : ℕ} (φ : productStabilizer L.prod ≃ₐ[ℂ] (Fin t → ℂ)) (j : Fin t)
    (heA : (reducedBlockIdempotent (productStabilizer L.prod) φ j).1 ≠ 0)
    (d : ℕ) (hmode : ∀ U ∈ L, d ≤ Module.finrank ℂ
      (cornerBlockSpace (K := ℂ) (reducedBlockIdempotent (productStabilizer L.prod) φ j) U)) :
    L.length * d + 2 ≤
      Module.finrank ℂ (IdempotentCorner (reducedBlockIdempotent (productStabilizer L.prod) φ j).1) +
      Module.finrank ℂ (IdempotentCorner (reducedBlockIdempotent (productStabilizer L.prod) φ j).2) +
      L.length := by
  let e := reducedBlockIdempotent (productStabilizer L.prod) φ j
  have he : e * e = e := reducedBlockIdempotent_mul_self (productStabilizer L.prod) φ j
  have heW : e ∈ productStabilizer L.prod := reducedBlockIdempotent_mem (productStabilizer L.prod) φ j
  have hlow := primitive_corner_list_dimension_bound Λ L hne hone hFrob hann hproj φ j
  have hupp := cornerBlockSpace_finrank_upper e he Λ L.prod heW hFrob hann heA
  have hsum : L.length * d ≤
      ((L.map (cornerBlockSpace (K := ℂ) e)).map
        (fun U : Submodule ℂ (IdempotentCorner e.1 × IdempotentCorner e.2) =>
          Module.finrank ℂ U)).sum := by
    have aux : ∀ P : List (Submodule ℂ (A × C)),
        (∀ U ∈ P, d ≤ Module.finrank ℂ (cornerBlockSpace (K := ℂ) e U)) →
        P.length * d ≤ ((P.map (cornerBlockSpace (K := ℂ) e)).map
          (fun U : Submodule ℂ (IdempotentCorner e.1 × IdempotentCorner e.2) =>
            Module.finrank ℂ U)).sum := by
      intro P
      induction P with
      | nil => simp
      | cons U P ih =>
          intro hP
          have hU := hP U (by simp)
          have htail := ih (fun V hV => hP V (by simp [hV]))
          simp only [List.length_cons, Nat.succ_mul, List.map_cons, List.sum_cons]
          omega
    exact aux L hmode
  have hlen : 1 ≤ L.length := List.length_pos_iff.mpr hne
  dsimp only [e] at hsum hupp
  omega

#assert_trust kernel cornerBlock_list_allbutone_projection
#assert_trust kernel cornerBlockFunctional_ne_zero
#assert_trust kernel primitive_corner_list_dimension_bound
#assert_trust kernel cornerBlockSpace_finrank_upper
#assert_trust kernel primitive_corner_block_dimension_inequality
#print axioms primitive_corner_block_dimension_inequality

end
end NLA.Proofs.TR14
