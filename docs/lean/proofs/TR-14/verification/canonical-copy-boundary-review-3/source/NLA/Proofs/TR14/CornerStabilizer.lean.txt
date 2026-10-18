import NLA.Proofs.TR14.CornerContext
import NLA.Proofs.TR14.ReducedPrimitiveBlocks

/-! A stabilizer in an actual primitive corner extends by zero to an ambient
stabilizer. The actual primitive scalar-action identity then forces it to be
a scalar multiple of that corner's identity. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

noncomputable section
variable {A C : Type*} [CommRing A] [CommRing C] [Algebra ℂ A] [Algebra ℂ C]

@[simp] theorem cornerBlockInclusion_idempotent_mul (e : A × C) (he : e * e = e)
    (x : IdempotentCorner e.1 × IdempotentCorner e.2) :
    e * cornerBlockInclusion (K := ℂ) e he x = cornerBlockInclusion (K := ℂ) e he x := by
  apply Prod.ext <;> simp only [cornerBlockInclusion, LinearMap.prodMap_apply,
    Prod.fst_mul, Prod.snd_mul, cornerInclusion_idempotent_mul]

/-- Every intrinsic block stabilizer extends by the actual ambient inclusion
 to a stabilizer of the original full product space. -/
theorem cornerBlock_stabilizer_inclusion (W : Submodule ℂ (A × C))
    (e : A × C) (he : e * e = e) (heW : e ∈ productStabilizer W)
    (z : IdempotentCorner e.1 × IdempotentCorner e.2)
    (hz : z ∈ productStabilizer (cornerBlockSpace (K := ℂ) e W)) :
    cornerBlockInclusion (K := ℂ) e he z ∈ productStabilizer W := by
  intro w hw
  have hq : cornerBlockProjection (K := ℂ) e w ∈ cornerBlockSpace (K := ℂ) e W :=
    ⟨w, hw, rfl⟩
  obtain ⟨a, ha, hqa⟩ := hz (cornerBlockProjection (K := ℂ) e w) hq
  have hmem : cornerBlockInclusion (K := ℂ) e he
      (z * cornerBlockProjection (K := ℂ) e w) ∈ W := by
    rw [← hqa]
    change cornerBlockInclusion (K := ℂ) e he (cornerBlockProjection (K := ℂ) e a) ∈ W
    rw [cornerBlockInclusion_projection]
    exact heW a ha
  have heq : cornerBlockInclusion (K := ℂ) e he
      (z * cornerBlockProjection (K := ℂ) e w) =
        cornerBlockInclusion (K := ℂ) e he z * w := by
    rw [cornerBlockInclusion_mul, cornerBlockInclusion_projection]
    calc
      cornerBlockInclusion (K := ℂ) e he z * (e * w) =
          (e * cornerBlockInclusion (K := ℂ) e he z) * w := by ring
      _ = cornerBlockInclusion (K := ℂ) e he z * w := by
        rw [cornerBlockInclusion_idempotent_mul]
  exact heq ▸ hmem

/-- For an actual primitive idempotent of the actual full stabilizer, every
intrinsic block stabilizer is an actual scalar multiple of its identity. -/
theorem primitive_corner_stabilizer_scalar (W : Submodule ℂ (A × C)) {t : ℕ}
    (φ : productStabilizer W ≃ₐ[ℂ] (Fin t → ℂ)) (j : Fin t)
    (z : IdempotentCorner (reducedBlockIdempotent (productStabilizer W) φ j).1 ×
      IdempotentCorner (reducedBlockIdempotent (productStabilizer W) φ j).2)
    (hz : z ∈ productStabilizer
      (cornerBlockSpace (K := ℂ) (reducedBlockIdempotent (productStabilizer W) φ j) W)) :
    ∃ c : ℂ, z = c • 1 := by
  let e := reducedBlockIdempotent (productStabilizer W) φ j
  have he : e * e = e := reducedBlockIdempotent_mul_self (productStabilizer W) φ j
  have heW : e ∈ productStabilizer W := reducedBlockIdempotent_mem (productStabilizer W) φ j
  let a := cornerBlockInclusion (K := ℂ) e he z
  have ha : a ∈ productStabilizer W := cornerBlock_stabilizer_inclusion W e he heW z hz
  let c := φ ⟨a, ha⟩ j
  have hscalar : a * e = c • e :=
    reducedBlockIdempotent_scalar_action (productStabilizer W) φ ⟨a, ha⟩ j
  have hfix : a * e = a := by
    simpa only [mul_comm] using cornerBlockInclusion_idempotent_mul e he z
  refine ⟨c, ?_⟩
  apply cornerBlockInclusion_injective (K := ℂ) e he
  rw [map_smul, cornerBlockInclusion_one]
  exact hfix.symm.trans hscalar

/-- The actual primitive block stabilizer has at most one scalar dimension,
including the possible zero corner. -/
theorem primitive_corner_stabilizer_finrank_le_one [FiniteDimensional ℂ A]
    [FiniteDimensional ℂ C] (W : Submodule ℂ (A × C)) {t : ℕ}
    (φ : productStabilizer W ≃ₐ[ℂ] (Fin t → ℂ)) (j : Fin t) :
    Module.finrank ℂ (productStabilizer
      (cornerBlockSpace (K := ℂ) (reducedBlockIdempotent (productStabilizer W) φ j) W)) ≤ 1 := by
  let e := reducedBlockIdempotent (productStabilizer W) φ j
  let B := IdempotentCorner e.1 × IdempotentCorner e.2
  have hle : (productStabilizer (cornerBlockSpace (K := ℂ) e W)).toSubmodule ≤
      Submodule.span ℂ ({(1 : B)} : Set B) := by
    intro z hz
    obtain ⟨c, rfl⟩ := primitive_corner_stabilizer_scalar W φ j z hz
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton 1))
  have hd := Submodule.finrank_mono hle
  have hs : Module.finrank ℂ (Submodule.span ℂ ({(1 : B)} : Set B)) ≤ 1 := by
    simpa using (finrank_span_le_card ({(1 : B)} : Set B))
  exact hd.trans hs

#assert_trust kernel cornerBlock_stabilizer_inclusion
#assert_trust kernel primitive_corner_stabilizer_scalar
#assert_trust kernel primitive_corner_stabilizer_finrank_le_one
#print axioms primitive_corner_stabilizer_finrank_le_one

end
end NLA.Proofs.TR14
