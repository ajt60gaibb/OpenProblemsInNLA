/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Original counterexample and mathematical proof: Matthew J. Colbrook.
AI-assisted auxiliary coordinate invariance proof; no complete verification claimed.
-/
import NLA.TR27.AffineBorder

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27
variable {W U : Type*} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem transport_cone (X : ProjectiveVariety W) (e : W ≃ₗ[ℂ] U) :
    (X.transport e).cone = e '' X.cone := by
  ext y
  constructor
  · intro hy
    exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    change X.coordinates (e.symm (e x)) ∈ MvPolynomial.zeroLocus ℂ X.ideal
    change X.coordinates x ∈ MvPolynomial.zeroLocus ℂ X.ideal at hx
    simpa only [e.symm_apply_apply] using hx

theorem transport_admissible (X : ProjectiveVariety W) (e : W ≃ₗ[ℂ] U)
    (hX : X.Admissible) : (X.transport e).Admissible := by
  refine ⟨hX.1, hX.2.1, hX.2.2.1, ?_, ?_⟩
  · obtain ⟨v, hv, hne⟩ := hX.2.2.2.1
    exact ⟨e v, by rw [transport_cone]; exact ⟨v, hv, rfl⟩, e.map_ne_zero_iff.mpr hne⟩
  · rw [transport_cone]
    change Submodule.span ℂ (e.toLinearMap '' X.cone) = ⊤
    rw [← Submodule.map_span, hX.2.2.2.2, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective

theorem coneRankAtMost_transport (X : ProjectiveVariety W) (e : W ≃ₗ[ℂ] U)
    (r : ℕ) (v : W) :
    ConeRankAtMost (X.transport e).cone r (e v) ↔ ConeRankAtMost X.cone r v := by
  constructor
  · rintro ⟨k, hk, a, x, hx, heq⟩
    refine ⟨k, hk, a, fun i => e.symm (x i), hx, ?_⟩
    have h := congrArg e.symm heq
    simpa only [map_sum, map_smul, e.symm_apply_apply] using h
  · rintro ⟨k, hk, a, x, hx, heq⟩
    refine ⟨k, hk, a, fun i => e (x i), ?_, ?_⟩
    · intro i
      rw [transport_cone]
      exact ⟨x i, hx i, rfl⟩
    · simpa only [map_sum, map_smul] using congrArg e heq

theorem affine_rank_closure_transport (X : ProjectiveVariety W) (e : W ≃ₗ[ℂ] U)
    (r : ℕ) (v : W) :
    e v ∈ (X.transport e).affineClosure {w | ConeRankAtMost (X.transport e).cone r w} ↔
      v ∈ X.affineClosure {w | ConeRankAtMost X.cone r w} := by
  have himage : (X.transport e).coordinates '' {w | ConeRankAtMost (X.transport e).cone r w} =
      X.coordinates '' {w | ConeRankAtMost X.cone r w} := by
    ext c
    constructor
    · rintro ⟨w, hw, hc⟩
      refine ⟨e.symm w, ?_, hc⟩
      apply (coneRankAtMost_transport X e r (e.symm w)).mp
      simpa using hw
    · rintro ⟨w, hw, hc⟩
      refine ⟨e w, (coneRankAtMost_transport X e r w).mpr hw, ?_⟩
      change X.coordinates (e.symm (e w)) = c
      simpa only [e.symm_apply_apply] using hc
  simp only [ProjectiveVariety.affineClosure, Set.mem_preimage, himage]
  change X.coordinates (e.symm (e v)) ∈ _ ↔ X.coordinates v ∈ _
  rw [e.symm_apply_apply]
  rfl

theorem coordinate_transport (X : ProjectiveVariety W) (e : W ≃ₗ[ℂ] U)
    (hX : X.Admissible) (p : ℙ ℂ W) :
    (X.transport e).Admissible ∧
    projectiveRank (X.transport e).points
        (Projectivization.map e.toLinearMap e.injective p) = projectiveRank X.points p ∧
    borderRank (X.transport e)
        (Projectivization.map e.toLinearMap e.injective p) = borderRank X p := by
  have hXe := transport_admissible X e hX
  have hep : e p.rep ≠ 0 := e.map_ne_zero_iff.mpr p.rep_nonzero
  have hmap : Projectivization.map e.toLinearMap e.injective p =
      Projectivization.mk ℂ (e p.rep) hep := by
    conv_lhs => rw [← p.mk_rep, Projectivization.map_mk]
    rfl
  refine ⟨hXe, ?_, ?_⟩
  · unfold projectiveRank
    congr 1
    ext r
    change ProjectiveRankAtMost (X.transport e).points r
      (Projectivization.map e.toLinearMap e.injective p) ↔ ProjectiveRankAtMost X.points r p
    rw [hmap, projective_cone_rank (X.transport e) hXe, coneRankAtMost_transport]
    simpa only [p.mk_rep] using (projective_cone_rank X hX r p.rep p.rep_nonzero).symm
  · unfold borderRank
    congr 1
    ext r
    change Projectivization.map e.toLinearMap e.injective p ∈
      (X.transport e).zariskiClosure {q | ProjectiveRankAtMost (X.transport e).points r q} ↔
      p ∈ X.zariskiClosure {q | ProjectiveRankAtMost X.points r q}
    rw [hmap, projective_affine_border (X.transport e) hXe, affine_rank_closure_transport]
    simpa only [p.mk_rep] using (projective_affine_border X hX r p.rep p.rep_nonzero).symm

#print axioms coordinate_transport
end NLA.TR27
