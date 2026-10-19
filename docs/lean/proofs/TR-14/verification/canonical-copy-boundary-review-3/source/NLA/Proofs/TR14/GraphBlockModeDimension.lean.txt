import NLA.Proofs.TR14.GraphQuotientContext
import NLA.Proofs.TR14.CornerContext
import NLA.Proofs.TR14.BlockPolynomialImage

/-! Exact polynomial first-image dimensions of actual corner-projected,
separately normalized graph modes. This proves the mode lower bound needed
by the block contextual inequality, without assuming quotient rank data. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.TR14
noncomputable section

/-- Actual quotient-mode multiplication is the actual block coefficient map. -/
theorem mul_quotientModeLinear_eq_blockMode (g : Polynomial ℂ) (e : AdjoinRoot g)
    (q : ℕ) (p : Fin (q + 1) → ℂ) :
    e * quotientModeLinear g q p = blockModeLinear g e (q + 1) p := by
  simp only [quotientModeLinear_apply, quotientMode, blockModeLinear,
    Finset.mul_sum, mul_smul_comm]
  rfl

/-- Projecting the mode to a genuine idempotent corner has exactly the
same dimension as the actual ambient polynomial multiplication image. -/
theorem corner_quotient_mode_image_finrank (g : Polynomial ℂ) (hg : g.Monic)
    (e : AdjoinRoot g) (he : e * e = e) (q : ℕ) :
    Module.finrank ℂ ((LinearMap.range (quotientModeLinear g q)).map
      (cornerProjection (K := ℂ) e).toLinearMap) =
      min (q + 1) (Module.finrank ℂ (IdempotentCorner e)) := by
  let M := (LinearMap.range (quotientModeLinear g q)).map (cornerProjection (K := ℂ) e).toLinearMap
  have hmap : M.map (cornerInclusion (K := ℂ) e he) =
      LinearMap.range (blockModeLinear g e (q + 1)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, ⟨p, rfl⟩, rfl⟩, rfl⟩
      exact ⟨p, (mul_quotientModeLinear_eq_blockMode g e q p).symm⟩
    · rintro ⟨p, rfl⟩
      refine ⟨cornerProjection (K := ℂ) e (quotientModeLinear g q p),
        ⟨quotientModeLinear g q p, ⟨p, rfl⟩, rfl⟩, ?_⟩
      exact mul_quotientModeLinear_eq_blockMode g e q p
  calc
    Module.finrank ℂ M = Module.finrank ℂ (M.map (cornerInclusion (K := ℂ) e he)) :=
      (Submodule.equivMapOfInjective (cornerInclusion (K := ℂ) e he)
        (cornerInclusion_injective (K := ℂ) e he) M).finrank_eq
    _ = min (q + 1) (Module.finrank ℂ (blockIdeal g e)) := by
      rw [hmap]
      exact blockModeLinear_finrank_range g hg e (q + 1)
    _ = min (q + 1) (Module.finrank ℂ (IdempotentCorner e)) := by
      rw [corner_finrank (K := ℂ) e he]
      rfl

/-- The first corner projection of an actual separately normalized graph
mode is exactly a unit-scaled quotient polynomial image. -/
theorem normalizedGraph_corner_fst_image {m q r : ℕ}
    (g : Polynomial ℂ) (u : Fin r → Fin m → Fin (q + 1) → ℂ)
    (a : Fin m → (AdjoinRoot g × (Fin r → ℂ))ˣ)
    (e : AdjoinRoot g × (Fin r → ℂ)) (k : Fin m) :
    (cornerBlockSpace (K := ℂ) e
      (normalizedGraphSpace (quotientModeLinear g q) u a k)).map
        (AlgHom.fst ℂ (IdempotentCorner e.1) (IdempotentCorner e.2)).toLinearMap =
      unitScale (Units.map
        (((cornerProjection (K := ℂ) e.1).comp
          (AlgHom.fst ℂ (AdjoinRoot g) (Fin r → ℂ))).toMonoidHom) (a k)⁻¹)
        ((LinearMap.range (quotientModeLinear g q)).map (cornerProjection (K := ℂ) e.1).toLinearMap) := by
  let f := (cornerProjection (K := ℂ) e.1).comp (AlgHom.fst ℂ (AdjoinRoot g) (Fin r → ℂ))
  have hcomp : (cornerBlockSpace (K := ℂ) e
      (normalizedGraphSpace (quotientModeLinear g q) u a k)).map
        (AlgHom.fst ℂ (IdempotentCorner e.1) (IdempotentCorner e.2)).toLinearMap =
      (normalizedGraphSpace (quotientModeLinear g q) u a k).map f.toLinearMap := by
    rw [cornerBlockSpace, ← Submodule.map_comp]
    rfl
  rw [hcomp, normalizedGraphSpace, unitScale_map]
  congr 1
  have hcomp' : (ordinaryGraphSpace (quotientModeLinear g q) u k).map f.toLinearMap =
      ((ordinaryGraphSpace (quotientModeLinear g q) u k).map
        (AlgHom.fst ℂ (AdjoinRoot g) (Fin r → ℂ)).toLinearMap).map
          (cornerProjection (K := ℂ) e.1).toLinearMap := by
    rw [← Submodule.map_comp]
    rfl
  rw [hcomp', ordinaryGraphSpace_fst]

/-- Actual lower dimension of every intrinsic block mode, including
arbitrary mode-dependent ordinary factors and zero idempotents. -/
theorem normalizedGraph_corner_mode_finrank_lower {m q r : ℕ}
    (g : Polynomial ℂ) (hg : g.Monic)
    (u : Fin r → Fin m → Fin (q + 1) → ℂ)
    (a : Fin m → (AdjoinRoot g × (Fin r → ℂ))ˣ)
    (e : AdjoinRoot g × (Fin r → ℂ)) (he : e * e = e) (k : Fin m) :
    min (q + 1) (Module.finrank ℂ (IdempotentCorner e.1)) ≤
      Module.finrank ℂ (cornerBlockSpace (K := ℂ) e
        (normalizedGraphSpace (quotientModeLinear g q) u a k)) := by
  let : Module.Finite ℂ (AdjoinRoot g) := hg.finite_adjoinRoot
  have hle := Submodule.finrank_map_le
    (AlgHom.fst ℂ (IdempotentCorner e.1) (IdempotentCorner e.2)).toLinearMap
    (cornerBlockSpace (K := ℂ) e (normalizedGraphSpace (quotientModeLinear g q) u a k))
  rw [normalizedGraph_corner_fst_image, finrank_unitScale,
    corner_quotient_mode_image_finrank g hg e.1 (congrArg Prod.fst he) q] at hle
  exact hle

#assert_trust kernel corner_quotient_mode_image_finrank
#assert_trust kernel normalizedGraph_corner_fst_image
#assert_trust kernel normalizedGraph_corner_mode_finrank_lower
#print axioms normalizedGraph_corner_mode_finrank_lower

end
end NLA.Proofs.TR14
