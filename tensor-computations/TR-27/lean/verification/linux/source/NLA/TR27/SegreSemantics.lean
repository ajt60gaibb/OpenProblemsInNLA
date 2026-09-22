/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Original counterexample and mathematical proof: Matthew J. Colbrook.
AI-assisted auxiliary semantic proofs; no complete TR-27 verification is claimed.
-/
import NLA.TR27.Semantics

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem represents_smul_iff (v : W) (p : ℙ ℂ W) (a : ℂ) (ha : a ≠ 0) :
    Represents (a • v) p ↔ Represents v p := by
  constructor
  · rintro ⟨b, hb, heq⟩
    exact ⟨b * a, mul_ne_zero hb ha, by simpa [smul_smul] using heq⟩
  · rintro ⟨b, hb, heq⟩
    exact ⟨b / a, div_ne_zero hb ha, by simpa [smul_smul, ha] using heq⟩

theorem segre_mk_mem (X : ProjectiveVariety W) (hX : X.Admissible)
    (x y : W) (hx : x ≠ 0) (hy : y ≠ 0) (hxc : x ∈ X.cone) (hyc : y ∈ X.cone) :
    Projectivization.mk ℂ (x ⊗ₜ[ℂ] y) (nonzero_tmul x y hx hy) ∈ segrePoints X.points := by
  refine ⟨Projectivization.mk ℂ x hx, (cone_projective_membership X hX x hx).mpr hxc,
    Projectivization.mk ℂ y hy, (cone_projective_membership X hX y hy).mpr hyc, ?_⟩
  obtain ⟨a, ha, heqx⟩ := represents_mk x hx
  obtain ⟨b, hb, heqy⟩ := represents_mk y hy
  rw [heqx, heqy, TensorProduct.smul_tmul_smul]
  apply (represents_smul_iff _ _ (a * b) (mul_ne_zero ha hb)).mpr
  exact represents_mk _ _

theorem segre_cone_rank (X : ProjectiveVariety W) (hX : X.Admissible)
    (r : ℕ) (z : W ⊗[ℂ] W) (q : ℙ ℂ (W ⊗[ℂ] W)) (hq : Represents z q) :
    ProjectiveRankAtMost (segrePoints X.points) r q ↔
      TensorRankAtMost X.cone r z := by
  classical
  have hz := represents_nonzero z q hq
  have heq := (represents_iff_eq_mk z hz q).mp hq
  rw [heq]
  constructor
  · rintro ⟨k, hk, p, hp, hspan⟩
    obtain ⟨a, ha⟩ := (projective_span_range k p z hz).mp hspan
    change ∀ i, ∃ x ∈ X.points, ∃ y ∈ X.points,
      ∃ b : ℂ, b ≠ 0 ∧ (p i).rep = b • (x.rep ⊗ₜ[ℂ] y.rep) at hp
    choose x hx y hy b hb hrep using hp
    refine ⟨k, hk, fun i => a i * b i, fun i => (x i).rep, fun i => (y i).rep,
      fun i => ⟨hx i, hy i⟩, ?_⟩
    rw [ha]
    apply Finset.sum_congr rfl
    intro i _
    rw [hrep, smul_smul]
  · rintro ⟨k, hk, a, x, y, hxy, hsum⟩
    obtain ⟨x₀, hxc₀, hx₀⟩ := hX.2.2.2.1
    let p : Fin k → ℙ ℂ (W ⊗[ℂ] W) := fun i =>
      if hi : x i ⊗ₜ[ℂ] y i = 0 then
        Projectivization.mk ℂ (x₀ ⊗ₜ[ℂ] x₀) (nonzero_tmul x₀ x₀ hx₀ hx₀)
      else Projectivization.mk ℂ (x i ⊗ₜ[ℂ] y i) hi
    refine ⟨k, hk, p, ?_, ?_⟩
    · intro i
      dsimp [p]
      split_ifs with hi
      · exact segre_mk_mem X hX x₀ x₀ hx₀ hx₀ hxc₀ hxc₀
      · have hx : x i ≠ 0 := by intro h; apply hi; simp [h]
        have hy : y i ≠ 0 := by intro h; apply hi; simp [h]
        exact segre_mk_mem X hX (x i) (y i) hx hy (hxy i).1 (hxy i).2
    · rw [projective_span_mk, hsum]
      apply Submodule.sum_mem
      intro i _
      apply Submodule.smul_mem
      by_cases hi : x i ⊗ₜ[ℂ] y i = 0
      · rw [hi]
        exact Submodule.zero_mem _
      · apply (projective_span_mk (Set.range p) (x i ⊗ₜ[ℂ] y i) hi).mp
        have hmem := Projectivization.Subspace.subset_span (Set.range p) (Set.mem_range_self i)
        simpa [p, hi] using hmem


/-- Separate products of two spanning cones span the actual tensor product. -/
theorem tensor_rank_exists (C : Set W) (hC : Submodule.span ℂ C = ⊤)
    (z : W ⊗[ℂ] W) : ∃ r, TensorRankAtMost C r z := by
  classical
  let D := Set.image2 (fun x y : W => x ⊗ₜ[ℂ] y) C C
  have hD : Submodule.span ℂ D = ⊤ := by
    change Submodule.span ℂ (Set.image2 (fun x y => TensorProduct.mk ℂ W W x y) C C) = ⊤
    rw [← Submodule.map₂_span_span, hC, TensorProduct.map₂_mk_top_top_eq_top]
  obtain ⟨r, k, hk, a, t, ht, hz⟩ := cone_rank_exists D hD z
  change ∀ i, ∃ x ∈ C, ∃ y ∈ C, x ⊗ₜ[ℂ] y = t i at ht
  choose x hx y hy hxy using ht
  refine ⟨r, k, hk, a, x, y, fun i => ⟨hx i, hy i⟩, ?_⟩
  simpa only [hxy] using hz

theorem segre_rank_minimum (X : ProjectiveVariety W) (hX : X.Admissible)
    (q : ℙ ℂ (W ⊗[ℂ] W)) :
    (∃ r, ProjectiveRankAtMost (segrePoints X.points) r q) ∧
    (∀ r, ProjectiveRankAtMost (segrePoints X.points) r q ↔
      projectiveRank (segrePoints X.points) q ≤ r) := by
  have hq : Represents q.rep q := ⟨1, one_ne_zero, (one_smul ℂ q.rep).symm⟩
  have hex : ∃ r, ProjectiveRankAtMost (segrePoints X.points) r q := by
    obtain ⟨r, hr⟩ := tensor_rank_exists X.cone hX.2.2.2.2 q.rep
    exact ⟨r, (segre_cone_rank X hX r q.rep q hq).mpr hr⟩
  exact ⟨hex, nat_predicate_iff_inf_le _ hex
    (fun h => projectiveRankAtMost_mono (segrePoints X.points) q h)⟩

#print axioms segre_rank_minimum
#print axioms segre_cone_rank
end NLA.TR27
