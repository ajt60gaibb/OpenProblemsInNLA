import NLA.Proofs.TR06.ModelChartDerivative
import NLA.TR06.MetricSlope

/-! Actual regularity separates all normalized permutation branches: radial
variations imply linear independence of the genuine summand tensors. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.NormalizedGraphCharts
open scoped BigOperators
open NLA.TR06
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem rankOneTangent_radial (j₀ : Fin d) (A : Tensor ℝ d n)
    (hA : NLA.Statements.TR06.RankOne A) (c : ℝ) :
    NLA.Statements.TR06.RankOneTangent A (c • A) := by
  classical
  obtain ⟨_hne,u,hu⟩ := hA
  let v : (j : Fin d) → Fin (n j) → ℝ := Function.update 0 j₀ (c • u j₀)
  refine ⟨u,v,hu,?_⟩
  rw [hu]
  ext q
  change c * (∏ k, u k (q k)) = ∑ j, ∏ k, if k=j then v k (q k) else u k (q k)
  rw [Finset.sum_eq_single j₀]
  · have h := congrArg (fun B : Tensor ℝ d n => B q) (pureTensor_smul_factor u j₀ c)
    change (∏ k, Function.update u j₀ (fun w => c * u j₀ w) k (q k)) =
      c * ∏ k, u k (q k) at h
    rw [← h]
    apply Finset.prod_congr rfl
    intro k _
    by_cases hk : k=j₀
    · subst k
      simp [v]
    · simp [v,Function.update_of_ne hk,hk]
  · intro j _ hj
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [v,Function.update_of_ne hj]
  · simp

theorem regularDecomposition_linearIndependent (j₀ : Fin d)
    (a : Fin r → Tensor ℝ d n) (ha : ∀ i, NLA.Statements.TR06.RankOne (a i))
    (hreg : NLA.Statements.TR06.RegularDecomposition a) : LinearIndependent ℝ a := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hsum i
  have hz := hreg (fun k => c k • a k)
    (fun k => rankOneTangent_radial j₀ (a k) (ha k) (c k)) hsum i
  exact (smul_eq_zero.mp hz).resolve_right (ha i).1

theorem chart_summands_linearIndependent (c : SmoothDecompositionChart d n r) (j₀ : Fin d)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source) :
    LinearIndependent ℝ (c.summands u) :=
  regularDecomposition_linearIndependent j₀ (c.summands u)
    (fun i => (Model.rankOne_iff _).mpr ((c.decomposes u hu).1 i))
    (Model.chart_regularDecomposition c j₀ u hu)

theorem normalizedTuple_permutation_stabilizer (a : Fin r → Tensor ℝ d n)
    (ha : ∀ i, a i ≠ 0) (hli : LinearIndependent ℝ a) (σ : Equiv.Perm (Fin r))
    (heq : permuteAngular σ (normalizedTuple a) = normalizedTuple a) : σ = Equiv.refl _ := by
  apply Equiv.ext
  intro i
  apply hli.eq_of_smul_apply_eq_smul_apply (‖a (σ i)‖⁻¹) (‖a i‖⁻¹) (σ i) i
    (inv_ne_zero (norm_ne_zero_iff.mpr (ha (σ i))))
  ext q
  have h := congrArg (fun X : AngularOutput d n r => X (i,q)) heq
  simpa only [permuteAngular_apply,normalizedTuple,PiLp.smul_apply,smul_eq_mul,
    div_eq_mul_inv,mul_comm] using h

theorem chart_normalizedTuple_permutation_stabilizer
    (c : SmoothDecompositionChart d n r) (j₀ : Fin d)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source)
    (σ : Equiv.Perm (Fin r))
    (heq : permuteAngular σ (normalizedTuple (c.summands u)) = normalizedTuple (c.summands u)) :
    σ = Equiv.refl _ :=
  normalizedTuple_permutation_stabilizer (c.summands u)
    (fun i => ((c.decomposes u hu).1 i).1) (chart_summands_linearIndependent c j₀ u hu) σ heq

#assert_trust kernel rankOneTangent_radial
#assert_trust kernel regularDecomposition_linearIndependent
#assert_trust kernel chart_summands_linearIndependent
#assert_trust kernel normalizedTuple_permutation_stabilizer
#assert_trust kernel chart_normalizedTuple_permutation_stabilizer
#print axioms chart_normalizedTuple_permutation_stabilizer
end NLA.Proofs.TR06.NormalizedGraphCharts
