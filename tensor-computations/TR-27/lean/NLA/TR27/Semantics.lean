/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Original counterexample and mathematical proof: Matthew J. Colbrook.
AI-assisted auxiliary semantic proofs; no complete TR-27 verification is claimed.
-/
import NLA.TR27.Definitions
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27
variable {W U : Type*} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem finite_coordinates [FiniteDimensional ℂ W] :
    ∃ n : ℕ, Nonempty (W ≃ₗ[ℂ] (Fin n → ℂ)) :=
  ⟨Module.finrank ℂ W, ⟨(Module.finBasis ℂ W).equivFun⟩⟩

theorem represents_mk (v : W) (hv : v ≠ 0) :
    Represents v (Projectivization.mk ℂ v hv) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  exact ⟨(a : ℂ), a.ne_zero, ha.symm⟩

theorem represents_iff_eq_mk (v : W) (hv : v ≠ 0) (p : ℙ ℂ W) :
    Represents v p ↔ p = Projectivization.mk ℂ v hv := by
  constructor
  · rintro ⟨a, ha, heq⟩
    rw [← Projectivization.mk_rep p, Projectivization.mk_eq_mk_iff']
    exact ⟨a, heq.symm⟩
  · rintro rfl
    exact represents_mk v hv

theorem represents_nonzero (v : W) (p : ℙ ℂ W) (h : Represents v p) : v ≠ 0 := by
  rintro rfl
  obtain ⟨a, ha, heq⟩ := h
  exact p.rep_nonzero (by simpa using heq)

theorem nonzero_tmul (x : W) (y : U) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one ℂ hy
  intro h
  have e := congrArg (fun z => (TensorProduct.lid ℂ ℂ) (TensorProduct.map f g z)) h
  simp [hf, hg] at e

theorem tensor_representatives (x y : W) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ⊗ₜ[ℂ] y ≠ 0 ∧ ∃! q : ℙ ℂ (W ⊗[ℂ] W), Represents (x ⊗ₜ[ℂ] y) q := by
  have h := nonzero_tmul x y hx hy
  exact ⟨h, Projectivization.mk ℂ _ h, represents_mk _ h,
    fun q hq => (represents_iff_eq_mk _ h q).mp hq⟩


/-- Evaluation of every homogeneous polynomial respects scalar multiplication. -/
theorem homogeneous_eval_smul {σ : Type*} (f : MvPolynomial σ ℂ) (d : ℕ)
    (hf : f.IsHomogeneous d) (a : ℂ) (v : σ → ℂ) :
    MvPolynomial.eval (a • v) f = a ^ d * MvPolynomial.eval v f := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, ← hf.degree_eq_sum_deg_support hb]
  ac_rfl

/-- A homogeneous ideal's whole zero locus is closed under every nonzero scale. -/
theorem cone_smul (X : ProjectiveVariety W) (hX : X.Admissible)
    (a : ℂ) (v : W) (hv : v ∈ X.cone) : a • v ∈ X.cone := by
  change X.coordinates (a • v) ∈ MvPolynomial.zeroLocus ℂ X.ideal
  rw [map_smul]
  intro f hf
  change MvPolynomial.eval (a • X.coordinates v) f = 0
  rw [← MvPolynomial.sum_homogeneousComponent f, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  rw [homogeneous_eval_smul _ d (MvPolynomial.homogeneousComponent_mem d f)]
  have hz := hv (MvPolynomial.homogeneousComponent d f)
    (MvPolynomial.homogeneousComponent_mem_of_mem hX.1 hf d)
  change MvPolynomial.eval (X.coordinates v) (MvPolynomial.homogeneousComponent d f) = 0 at hz
  rw [hz, mul_zero]

theorem cone_smul_iff (X : ProjectiveVariety W) (hX : X.Admissible)
    (a : ℂ) (ha : a ≠ 0) (v : W) : a • v ∈ X.cone ↔ v ∈ X.cone := by
  constructor
  · intro hv
    have := cone_smul X hX a⁻¹ (a • v) hv
    simpa [smul_smul, ha] using this
  · exact cone_smul X hX a v

theorem cone_projective_membership (X : ProjectiveVariety W) (hX : X.Admissible)
    (v : W) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ X.points ↔ v ∈ X.cone := by
  obtain ⟨a, ha, heq⟩ := represents_mk v hv
  change (Projectivization.mk ℂ v hv).rep ∈ X.cone ↔ v ∈ X.cone
  rw [heq, cone_smul_iff X hX a ha]


/-- Projective span is exactly linear span of arbitrary chosen representatives. -/
theorem projective_span_rep (Y : Set (ℙ ℂ W)) (p : ℙ ℂ W) :
    p ∈ Projectivization.Subspace.span Y ↔
      p.rep ∈ Submodule.span ℂ (Projectivization.rep '' Y) := by
  let S := Submodule.span ℂ (Projectivization.rep '' Y)
  have h₁ : Projectivization.Subspace.span Y ≤ S.projectivization := by
    apply Projectivization.Subspace.span_le_subspace_iff.mpr
    intro q hq
    change q ∈ S.projectivization
    rw [← q.mk_rep, Submodule.mk_mem_projectivization_iff]
    exact Submodule.subset_span ⟨q, hq, rfl⟩
  have h₂ : S ≤ (Projectivization.Subspace.span Y).submodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, hq, rfl⟩
    change q.rep ∈ (Projectivization.Subspace.span Y).submodule
    rw [Projectivization.Subspace.mem_submodule_iff _ q.rep_nonzero, q.mk_rep]
    exact Projectivization.Subspace.subset_span Y hq
  constructor
  · intro hp
    have := h₁ hp
    rwa [← p.mk_rep, Submodule.mk_mem_projectivization_iff] at this
  · intro hp
    have := h₂ hp
    rwa [Projectivization.Subspace.mem_submodule_iff _ p.rep_nonzero, p.mk_rep] at this

theorem projective_span_mk (Y : Set (ℙ ℂ W)) (v : W) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ Projectivization.Subspace.span Y ↔
      v ∈ Submodule.span ℂ (Projectivization.rep '' Y) := by
  rw [projective_span_rep]
  obtain ⟨a, ha, heq⟩ := represents_mk v hv
  rw [heq, Submodule.smul_mem_iff _ ha]

/-- Finite projective span admits unrestricted complex coefficients. -/
theorem projective_span_range (k : ℕ) (q : Fin k → ℙ ℂ W) (v : W) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ Projectivization.Subspace.span (Set.range q) ↔
      ∃ a : Fin k → ℂ, v = ∑ i, a i • (q i).rep := by
  rw [projective_span_mk, ← Set.range_comp, Submodule.mem_span_range_iff_exists_fun]
  exact exists_congr (fun _ => eq_comm)


theorem projective_cone_rank (X : ProjectiveVariety W) (hX : X.Admissible)
    (r : ℕ) (v : W) (hv : v ≠ 0) :
    ProjectiveRankAtMost X.points r (Projectivization.mk ℂ v hv) ↔
      ConeRankAtMost X.cone r v := by
  classical
  constructor
  · rintro ⟨k, hk, q, hq, hp⟩
    obtain ⟨a, ha⟩ := (projective_span_range k q v hv).mp hp
    exact ⟨k, hk, a, fun i => (q i).rep, hq, ha⟩
  · rintro ⟨k, hk, a, x, hx, heq⟩
    obtain ⟨x₀, hx₀, hne₀⟩ := hX.2.2.2.1
    let q : Fin k → ℙ ℂ W := fun i =>
      if hi : x i = 0 then Projectivization.mk ℂ x₀ hne₀
      else Projectivization.mk ℂ (x i) hi
    refine ⟨k, hk, q, ?_, ?_⟩
    · intro i
      dsimp [q]
      split_ifs with hi
      · exact (cone_projective_membership X hX x₀ hne₀).mpr hx₀
      · exact (cone_projective_membership X hX (x i) hi).mpr (hx i)
    · rw [projective_span_mk, heq]
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      by_cases hxi : x i = 0
      · rw [hxi]
        exact Submodule.zero_mem _
      · apply (projective_span_mk (Set.range q) (x i) hxi).mp
        have hmem := Projectivization.Subspace.subset_span (Set.range q)
          (Set.mem_range_self i)
        simpa [q, hxi] using hmem


theorem cone_rank_exists (C : Set W) (hC : Submodule.span ℂ C = ⊤) (v : W) :
    ∃ r, ConeRankAtMost C r v := by
  classical
  have hv : v ∈ Submodule.span ℂ C := by rw [hC]; trivial
  obtain ⟨f, t, ht, _, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hv
  let e := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, Fintype.card t, le_rfl,
    fun i => f (e i), fun i => (e i).val, fun i => ht (e i).property, ?_⟩
  rw [← hsum]
  exact (Finset.sum_coe_sort t (fun w : W => f w • w)).symm.trans
    (e.sum_comp (fun w : t => f w • (w : W))).symm

theorem projective_rank_exists (X : ProjectiveVariety W) (hX : X.Admissible)
    (p : ℙ ℂ W) : ∃ r, ProjectiveRankAtMost X.points r p := by
  obtain ⟨r, hr⟩ := cone_rank_exists X.cone hX.2.2.2.2 p.rep
  refine ⟨r, ?_⟩
  have := (projective_cone_rank X hX r p.rep p.rep_nonzero).mpr hr
  simpa using this

theorem projectiveRankAtMost_mono (Y : Set (ℙ ℂ W)) (p : ℙ ℂ W)
    {r s : ℕ} (hrs : r ≤ s) : ProjectiveRankAtMost Y r p → ProjectiveRankAtMost Y s p := by
  rintro ⟨k, hk, q, hq, hp⟩
  exact ⟨k, hk.trans hrs, q, hq, hp⟩

theorem zariskiClosure_subset (X : ProjectiveVariety W) (Y : Set (ℙ ℂ W)) :
    Y ⊆ X.zariskiClosure Y := by
  intro p hp f d hf hY
  exact hY p hp

theorem zariskiClosure_mono (X : ProjectiveVariety W) {Y Z : Set (ℙ ℂ W)}
    (h : Y ⊆ Z) : X.zariskiClosure Y ⊆ X.zariskiClosure Z := by
  intro p hp f d hf hZ
  exact hp f d hf (fun q hq => hZ q (h hq))

theorem nat_predicate_iff_inf_le (P : ℕ → Prop) (hex : ∃ n, P n)
    (hmono : ∀ {r s}, r ≤ s → P r → P s) (r : ℕ) :
    P r ↔ sInf {n | P n} ≤ r := by
  constructor
  · exact fun h => csInf_le' h
  · intro h
    exact hmono h (csInf_mem hex)

theorem rank_minima (X : ProjectiveVariety W) (hX : X.Admissible) (p : ℙ ℂ W) :
    (∃ r, ProjectiveRankAtMost X.points r p) ∧
    (∀ r, ProjectiveRankAtMost X.points r p ↔ projectiveRank X.points p ≤ r) ∧
    (∃ r, p ∈ X.zariskiClosure {q | ProjectiveRankAtMost X.points r q}) ∧
    (∀ r, p ∈ X.zariskiClosure {q | ProjectiveRankAtMost X.points r q} ↔
      borderRank X p ≤ r) := by
  have hnonempty := projective_rank_exists X hX p
  have hbnonempty : ∃ r, p ∈ X.zariskiClosure {q | ProjectiveRankAtMost X.points r q} := by
    obtain ⟨r, hr⟩ := hnonempty
    exact ⟨r, zariskiClosure_subset X _ hr⟩
  refine ⟨hnonempty, ?_, hbnonempty, ?_⟩
  · exact nat_predicate_iff_inf_le _ hnonempty (fun h => projectiveRankAtMost_mono _ p h)
  · apply nat_predicate_iff_inf_le _ hbnonempty
    intro r s hrs hp
    exact zariskiClosure_mono X (fun q hq => projectiveRankAtMost_mono X.points q hrs hq) hp

#print axioms rank_minima
#print axioms projective_cone_rank
#print axioms projective_span_range
#print axioms cone_projective_membership
#print axioms finite_coordinates
#print axioms tensor_representatives
end NLA.TR27
