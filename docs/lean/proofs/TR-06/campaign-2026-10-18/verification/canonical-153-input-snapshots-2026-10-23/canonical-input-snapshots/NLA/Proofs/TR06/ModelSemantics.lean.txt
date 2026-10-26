import NLA.Statements.TR06
import NLA.TR06.Definitions

/-! Exact algebraic semantics shared by the published intrinsic boundary and
retained chart model. Neither statement presentation is changed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.TR06.Model
open scoped BigOperators
variable {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem outer_eq_pureTensor (u : (j : Fin d) → Fin (n j) → 𝕜) :
    NLA.Statements.TR06.Outer u = NLA.TR06.pureTensor u := rfl

theorem rankOne_iff (A : NLA.TR06.Tensor 𝕜 d n) :
    NLA.Statements.TR06.RankOne A ↔ NLA.TR06.RankOne A := by
  constructor
  · rintro ⟨hne,u,hu⟩
    exact ⟨hne,u,hu.symm⟩
  · rintro ⟨hne,u,hu⟩
    exact ⟨hne,u,hu.symm⟩

theorem decomposes_iff (A : NLA.TR06.Tensor 𝕜 d n)
    (a : Fin r → NLA.TR06.Tensor 𝕜 d n) :
    NLA.Statements.TR06.Decomposition A a ↔ NLA.TR06.Decomposes a A := by
  unfold NLA.Statements.TR06.Decomposition NLA.TR06.Decomposes
  simp_rw [rankOne_iff]

theorem exactRank_iff (A : NLA.TR06.Tensor 𝕜 d n) :
    NLA.Statements.TR06.ExactRank r A ↔ NLA.TR06.ExactRank r A := by
  unfold NLA.Statements.TR06.ExactRank NLA.TR06.ExactRank
  simp_rw [decomposes_iff]

/-- The retained presentations use opposite permutation orientations. -/
theorem identifiable_iff (A : NLA.TR06.Tensor 𝕜 d n) :
    NLA.Statements.TR06.UniqueSummands r A ↔ NLA.TR06.Identifiable r A := by
  constructor
  · intro h a b ha hb
    obtain ⟨σ,hσ⟩ := h a b ((decomposes_iff A a).mpr ha) ((decomposes_iff A b).mpr hb)
    refine ⟨σ.symm,fun i => ?_⟩
    simpa only [σ.apply_symm_apply] using (hσ (σ.symm i)).symm
  · intro h a b ha hb
    obtain ⟨σ,hσ⟩ := h a b ((decomposes_iff A a).mp ha) ((decomposes_iff A b).mp hb)
    refine ⟨σ.symm,fun i => ?_⟩
    simpa only [σ.apply_symm_apply] using (hσ (σ.symm i)).symm

theorem generic_iff :
    NLA.Statements.TR06.GenericComplexIdentifiable n r ↔
      NLA.TR06.GenericComplexIdentifiable d n r := by
  unfold NLA.Statements.TR06.GenericComplexIdentifiable NLA.TR06.GenericComplexIdentifiable
  simp_rw [exactRank_iff,identifiable_iff]

theorem dimension_eq (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    NLA.Statements.TR06.ManifoldDimension n r = NLA.TR06.expectedDimension d n r := rfl

theorem gaussianWeight_eq (A : NLA.TR06.Tensor ℝ d n) :
    NLA.Statements.TR06.GaussianWeight A = NLA.TR06.gaussianWeight A := rfl

/-- Every intrinsic regular point is at least an actual identifiable tensor.
No open embedded-chart or full-measure assertion is inferred here. -/
theorem smoothIdentifiable_subset_sampling :
    {A : NLA.TR06.Tensor ℝ d n | NLA.Statements.TR06.SmoothIdentifiable n r A} ⊆
      NLA.TR06.identifiableRealSet d n r := by
  intro A hA
  exact ⟨(exactRank_iff A).mp hA.1,(identifiable_iff A).mp hA.2.1⟩

#assert_trust kernel outer_eq_pureTensor
#assert_trust kernel rankOne_iff
#assert_trust kernel decomposes_iff
#assert_trust kernel exactRank_iff
#assert_trust kernel identifiable_iff
#assert_trust kernel generic_iff
#assert_trust kernel dimension_eq
#assert_trust kernel gaussianWeight_eq
#assert_trust kernel smoothIdentifiable_subset_sampling
#print axioms identifiable_iff
#print axioms generic_iff
#print axioms smoothIdentifiable_subset_sampling
end NLA.Proofs.TR06.Model
