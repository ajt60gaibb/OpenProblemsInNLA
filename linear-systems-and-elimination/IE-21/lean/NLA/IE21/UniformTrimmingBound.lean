import NLA.IE21.UniformTrimmingGeometry

/-!
Finite-net probability assembly for IE-21. The generic bound below exposes its
input probability estimates explicitly. It is not the frozen final theorem:
that declaration will follow only after its concentration and coupling inputs
are supplied by the separate proof modules.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
namespace NLA.IE21

theorem uniform_trim_probability_of_bounds (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hn : 1 ≤ n) (μ : Measure (Mat m n)) [IsProbabilityMeasure μ]
    (t ε δ : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ) (Bcov Bpoint : ℝ) (hBpoint : 0 ≤ Bpoint)
    (hcov : μ.real {A | covarianceError A > t} ≤ Bcov)
    (hpopulation : ∀ y : Space n, ‖y‖ = 1 →
      |populationTrim θ (sphereLaw n) (directionalEnergy y) - gaussianTrim θ| ≤
        Real.sqrt (2 / (n : ℝ)))
    (hpoint : ∀ y : Space n, ‖y‖ = 1 →
      μ.real {A | |directionalTrim θ A y -
        populationTrim θ (sphereLaw n) (directionalEnergy y)| >
          2 * truncationScale θ * ε + truncationScale θ / m} ≤ Bpoint) :
    μ.real (GoodEvent θ m n t ε δ)ᶜ ≤ Bcov + (1 + 2 / δ) ^ n * Bpoint := by
  classical
  obtain ⟨C, hC, hcard, hcover⟩ := sphere_net n hn δ hδ
  let B : Space n → Set (Mat m n) := fun y =>
    {A | |directionalTrim θ A y - populationTrim θ (sphereLaw n) (directionalEnergy y)| >
      2 * truncationScale θ * ε + truncationScale θ / m}
  have hsub : (GoodEvent θ m n t ε δ)ᶜ ⊆
      {A | covarianceError A > t} ∪ ⋃ y ∈ C, B y := by
    intro A hbad
    by_contra hout
    have hcovA : covarianceError A ≤ t :=
      le_of_not_gt (fun h => hout (Or.inl h))
    have hpointA : ∀ y ∈ C,
        |directionalTrim θ A y - populationTrim θ (sphereLaw n) (directionalEnergy y)| ≤
          2 * truncationScale θ * ε + truncationScale θ / m := by
      intro y hy
      apply le_of_not_gt
      intro h
      exact hout (Or.inr (mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, h⟩⟩))
    exact hbad (goodEvent_of_net θ hθ A t ε δ ht C hC hcover hcovA
      (fun y hy => hpopulation y (hC y hy)) hpointA)
  calc
    μ.real (GoodEvent θ m n t ε δ)ᶜ ≤
        μ.real ({A | covarianceError A > t} ∪ ⋃ y ∈ C, B y) := measureReal_mono hsub
    _ ≤ μ.real {A | covarianceError A > t} + ∑ y ∈ C, μ.real (B y) :=
      (measureReal_union_le _ _).trans
        (add_le_add le_rfl (measureReal_biUnion_finset_le (μ := μ) C B))
    _ ≤ Bcov + (C.card : ℝ) * Bpoint := by
      have hsum : (∑ y ∈ C, μ.real (B y)) ≤ ∑ _y ∈ C, Bpoint :=
        Finset.sum_le_sum fun y hy => hpoint y (hC y hy)
      simp only [Finset.sum_const, nsmul_eq_mul] at hsum
      exact add_le_add hcov hsum
    _ ≤ Bcov + (1 + 2 / δ) ^ n * Bpoint :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard hBpoint)

end NLA.IE21
