/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Original counterexample and mathematical proof: Matthew J. Colbrook.
AI-assisted auxiliary geometry proofs; no complete TR-27 verification is claimed.
-/
import NLA.TR27.Semantics

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Homogeneous equations vanishing on every projective point vanish on the
entire cone, including its origin and degree-zero equations. -/
theorem homogeneous_vanishes_on_cone (X : ProjectiveVariety W) (hX : X.Admissible)
    (f : MvPolynomial (Fin X.dimension) ℂ) (d : ℕ) (hf : f.IsHomogeneous d)
    (hpoints : ∀ p ∈ X.points, MvPolynomial.eval (X.coordinates p.rep) f = 0) :
    ∀ v ∈ X.cone, MvPolynomial.eval (X.coordinates v) f = 0 := by
  have hnonzero : ∀ v ∈ X.cone, v ≠ 0 →
      MvPolynomial.eval (X.coordinates v) f = 0 := by
    intro v hv hne
    have hp := hpoints (Projectivization.mk ℂ v hne)
      ((cone_projective_membership X hX v hne).mpr hv)
    obtain ⟨a, ha, heq⟩ := represents_mk v hne
    rw [heq, map_smul, homogeneous_eval_smul f d hf] at hp
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero d ha)
  intro v hv
  by_cases hne : v = 0
  · obtain ⟨v₀, hv₀, hne₀⟩ := hX.2.2.2.1
    have hz := homogeneous_eval_smul f d hf 0 (X.coordinates v₀)
    simpa only [hne, map_zero, zero_smul, hnonzero v₀ hv₀ hne₀, mul_zero] using hz
  · exact hnonzero v hv hne

/-- The complex-point Nullstellensatz identifies every homogeneous equation
vanishing on the projective point set with a member of the prime ideal. -/
theorem homogeneous_mem_ideal_of_vanishes (X : ProjectiveVariety W) (hX : X.Admissible)
    (f : MvPolynomial (Fin X.dimension) ℂ) (d : ℕ) (hf : f.IsHomogeneous d)
    (hpoints : ∀ p ∈ X.points, MvPolynomial.eval (X.coordinates p.rep) f = 0) :
    f ∈ X.ideal := by
  have hfzero : f ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ X.ideal) := by
    intro c hc
    change MvPolynomial.eval c f = 0
    have hv : X.coordinates.symm c ∈ X.cone := by
      change X.coordinates (X.coordinates.symm c) ∈ MvPolynomial.zeroLocus ℂ X.ideal
      simpa only [X.coordinates.apply_symm_apply] using hc
    have h := homogeneous_vanishes_on_cone X hX f d hf hpoints _ hv
    simpa only [X.coordinates.apply_symm_apply] using h
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ), hX.2.1.radical] at hfzero
  exact hfzero

theorem admissible_points_closed (X : ProjectiveVariety W) (hX : X.Admissible) :
    X.IsClosed X.points := by
  apply Set.Subset.antisymm
  · intro p hp
    change X.coordinates p.rep ∈ MvPolynomial.zeroLocus ℂ X.ideal
    intro f hf
    change MvPolynomial.eval (X.coordinates p.rep) f = 0
    rw [← MvPolynomial.sum_homogeneousComponent f, map_sum]
    apply Finset.sum_eq_zero
    intro d hd
    apply hp (MvPolynomial.homogeneousComponent d f) d
      (MvPolynomial.homogeneousComponent_mem d f)
    intro q hq
    exact hq _ (MvPolynomial.homogeneousComponent_mem_of_mem hX.1 hf d)
  · exact zariskiClosure_subset X X.points

theorem admissible_points_irreducible (X : ProjectiveVariety W) (hX : X.Admissible) :
    X.IsIrreducible X.points := by
  classical
  obtain ⟨v₀, hv₀, hne₀⟩ := hX.2.2.2.1
  refine ⟨⟨Projectivization.mk ℂ v₀ hne₀,
    (cone_projective_membership X hX v₀ hne₀).mpr hv₀⟩, ?_⟩
  intro A B hA hB hcover
  by_contra h
  obtain ⟨ha, hb⟩ := not_or.mp h
  obtain ⟨a, hax, haA⟩ := Set.not_subset.mp ha
  obtain ⟨b, hbx, hbB⟩ := Set.not_subset.mp hb
  have haClosure : a ∉ X.zariskiClosure A := by
    change X.zariskiClosure A = A at hA
    rwa [hA]
  have hbClosure : b ∉ X.zariskiClosure B := by
    change X.zariskiClosure B = B at hB
    rwa [hB]
  change ¬ (∀ (f : MvPolynomial (Fin X.dimension) ℂ) (d : ℕ),
    f.IsHomogeneous d →
    (∀ q ∈ A, MvPolynomial.eval (X.coordinates q.rep) f = 0) →
    MvPolynomial.eval (X.coordinates a.rep) f = 0) at haClosure
  change ¬ (∀ (f : MvPolynomial (Fin X.dimension) ℂ) (d : ℕ),
    f.IsHomogeneous d →
    (∀ q ∈ B, MvPolynomial.eval (X.coordinates q.rep) f = 0) →
    MvPolynomial.eval (X.coordinates b.rep) f = 0) at hbClosure
  push Not at haClosure hbClosure
  obtain ⟨f, d, hf, hfA, hfa⟩ := haClosure
  obtain ⟨g, e, hg, hgB, hgb⟩ := hbClosure
  have hfg : f * g ∈ X.ideal := by
    apply homogeneous_mem_ideal_of_vanishes X hX (f * g) (d + e) (hf.mul hg)
    intro p hp
    rw [map_mul]
    rcases hcover hp with hpA | hpB
    · rw [hfA p hpA, zero_mul]
    · rw [hgB p hpB, mul_zero]
  rcases hX.2.1.mem_or_mem hfg with hfI | hgI
  · exact hfa (hax f hfI)
  · exact hgb (hbx g hgI)

theorem admissible_points_span (X : ProjectiveVariety W) (hX : X.Admissible) :
    Projectivization.Subspace.span X.points = ⊤ := by
  apply le_antisymm le_top
  intro p hp
  rw [projective_span_rep]
  have hcone : X.cone ⊆ Submodule.span ℂ (Projectivization.rep '' X.points) := by
    intro v hv
    by_cases hne : v = 0
    · rw [hne]
      exact Submodule.zero_mem _
    · apply (projective_span_mk X.points v hne).mp
      exact Projectivization.Subspace.subset_span X.points
        ((cone_projective_membership X hX v hne).mpr hv)
  have hspan := Submodule.span_le.mpr hcone
  rw [hX.2.2.2.2] at hspan
  exact hspan (Submodule.mem_top)

/-- Algebraic admissibility entails actual closedness and irreducibility of
the full complex projective point set and its full projective span. -/
theorem admissible_geometry (X : ProjectiveVariety W) (hX : X.Admissible) :
    X.IsClosed X.points ∧ X.IsIrreducible X.points ∧
      Projectivization.Subspace.span X.points = ⊤ :=
  ⟨admissible_points_closed X hX, admissible_points_irreducible X hX,
    admissible_points_span X hX⟩

#print axioms admissible_geometry
end NLA.TR27
