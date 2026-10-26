import NLA.Proofs.TR06.ModelChartDerivative
import NLA.TR06.SourceBridge

/-! Exact equality between the frozen intrinsic tangent supremum and the
retained order-free metric slope, at every actual smooth chart point. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.Model
open scoped BigOperators Topology ENNReal
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem angularProductVariation_perm (a v : Fin r → NLA.TR06.Tensor ℝ d n)
    (σ : Equiv.Perm (Fin r)) :
    NLA.Statements.TR06.AngularProductVariation (a ∘ σ) (v ∘ σ) =
      NLA.TR06.permuteAngular σ (NLA.Statements.TR06.AngularProductVariation a v) := rfl

theorem norm_angularProductVariation_perm (a v : Fin r → NLA.TR06.Tensor ℝ d n)
    (σ : Equiv.Perm (Fin r)) :
    ‖NLA.Statements.TR06.AngularProductVariation (a ∘ σ) (v ∘ σ)‖ =
      ‖NLA.Statements.TR06.AngularProductVariation a v‖ := by
  rw [angularProductVariation_perm]
  exact (NLA.TR06.permuteAngular σ).norm_map _

theorem angularCondition_eq_chart_derivative (c : NLA.TR06.SmoothDecompositionChart d n r)
    (j₀ : Fin d) (u : EuclideanSpace ℝ (Fin (NLA.TR06.expectedDimension d n r)))
    (hu : u ∈ c.chart.source) :
    NLA.Statements.TR06.AngularCondition r (c.chart u).val =
      NLA.TR06.derivativeRatio (fderiv ℝ (fun y => (c.chart y).val) u)
        (fderiv ℝ (fun y => NLA.TR06.normalizedTuple (c.summands y)) u) := by
  classical
  have hdec := (decomposes_iff _ _).mpr (c.decomposes u hu)
  have hident := (identifiable_iff _).mpr (c.chart u).property.2
  apply le_antisymm
  · apply sSup_le
    rintro z ⟨a,v,ha,hv,hne,rfl⟩
    obtain ⟨σ,hσ⟩ := hident (c.summands u) a hdec ha
    have haeq : c.summands u = a ∘ σ := funext hσ
    have hperm : ∀ i, NLA.Statements.TR06.RankOneTangent (c.summands u i) ((v ∘ σ) i) := by
      intro i
      rw [hσ i]
      exact hv (σ i)
    obtain ⟨w,hw⟩ := (chart_tangent_range c j₀ u hu (v ∘ σ)).mp hperm
    have hinput : fderiv ℝ (fun y => (c.chart y).val) u w = ∑ i, v i := by
      rw [chart_input_derivative_sum c u w hu]
      simp_rw [hw]
      exact Equiv.sum_comp σ v
    have houtput : fderiv ℝ (fun y => NLA.TR06.normalizedTuple (c.summands y)) u w =
        NLA.Statements.TR06.AngularProductVariation (c.summands u) (v ∘ σ) := by
      rw [chart_output_derivative c u w hu]
      congr 1
      exact funext hw
    have hnorm : ‖NLA.Statements.TR06.AngularProductVariation (c.summands u) (v ∘ σ)‖ =
        ‖NLA.Statements.TR06.AngularProductVariation a v‖ := by
      rw [haeq]
      exact norm_angularProductVariation_perm a v σ
    calc
      _ = ENNReal.ofReal (‖fderiv ℝ (fun y => NLA.TR06.normalizedTuple (c.summands y)) u w‖ /
          ‖fderiv ℝ (fun y => (c.chart y).val) u w‖) := by rw [hinput,houtput,hnorm]
      _ ≤ _ := le_iSup (fun w => ENNReal.ofReal
        (‖fderiv ℝ (fun y => NLA.TR06.normalizedTuple (c.summands y)) u w‖ /
          ‖fderiv ℝ (fun y => (c.chart y).val) u w‖)) w
  · apply iSup_le
    intro w
    by_cases hz : fderiv ℝ (fun y => (c.chart y).val) u w = 0
    · have hw : w=0 := c.input_injective_derivative u hu (by simpa only [map_zero] using hz)
      simp only [hw,map_zero,norm_zero,zero_div,ENNReal.ofReal_zero]
      exact bot_le
    · let v := fun i => fderiv ℝ (fun y => c.summands y i) u w
      have hv : ∀ i, NLA.Statements.TR06.RankOneTangent (c.summands u i) (v i) :=
        (chart_tangent_range c j₀ u hu v).mpr ⟨w,fun _ => rfl⟩
      have hsum : (∑ i, v i) = fderiv ℝ (fun y => (c.chart y).val) u w :=
        (chart_input_derivative_sum c u w hu).symm
      apply le_sSup
      refine ⟨c.summands u,v,hdec,hv,?_,?_⟩
      · rwa [hsum]
      · rw [hsum,chart_output_derivative c u w hu]

theorem angularCondition_eq_angularSlope_at_chart (c : NLA.TR06.SmoothDecompositionChart d n r)
    (j₀ : Fin d) (u : EuclideanSpace ℝ (Fin (NLA.TR06.expectedDimension d n r)))
    (hu : u ∈ c.chart.source) :
    NLA.Statements.TR06.AngularCondition r (c.chart u).val =
      NLA.TR06.angularSlope r (c.chart u).val := by
  rw [angularCondition_eq_chart_derivative c j₀ u hu]
  exact (NLA.TR06.angularSlope_eq_chart_derivative c.toC1 u hu).symm

theorem angularCondition_eq_angularSlope_on_smoothRegular (j₀ : Fin d)
    (A : NLA.TR06.Tensor ℝ d n) (hA : A ∈ NLA.TR06.smoothRegularSet d n r) :
    NLA.Statements.TR06.AngularCondition r A = NLA.TR06.angularSlope r A := by
  obtain ⟨c,u,hu,rfl⟩ := hA
  exact angularCondition_eq_angularSlope_at_chart c j₀ u hu

theorem angularCondition_eq_sourceAngular_on_smoothRegular (j₀ : Fin d)
    (A : NLA.TR06.Tensor ℝ d n) (hA : A ∈ NLA.TR06.smoothRegularSet d n r) :
    NLA.Statements.TR06.AngularCondition r A = NLA.TR06.sourceAngular d n r A := by
  rw [angularCondition_eq_angularSlope_on_smoothRegular j₀ A hA,
    NLA.TR06.sourceAngular_eq_angularSlope_on_smoothRegularSet hA]

#assert_trust kernel angularProductVariation_perm
#assert_trust kernel norm_angularProductVariation_perm
#assert_trust kernel angularCondition_eq_chart_derivative
#assert_trust kernel angularCondition_eq_angularSlope_at_chart
#assert_trust kernel angularCondition_eq_angularSlope_on_smoothRegular
#assert_trust kernel angularCondition_eq_sourceAngular_on_smoothRegular
#print axioms angularCondition_eq_chart_derivative
#print axioms angularCondition_eq_angularSlope_on_smoothRegular
end NLA.Proofs.TR06.Model
