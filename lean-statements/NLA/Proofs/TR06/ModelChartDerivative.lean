import NLA.Proofs.TR06.ModelRegularity
import NLA.Proofs.TR06.ModelTupleNormalization

/-! Every genuine smooth decomposition chart has exactly the intrinsic
rank-one tangent tuples as its summand derivative range. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.Model
open scoped BigOperators Topology
open Filter
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem chart_decoder_eventuallyEq (c : NLA.TR06.SmoothDecompositionChart d n r)
    (q : Fin r → NLA.TR06.TensorIndex d n)
    (u : EuclideanSpace ℝ (Fin (NLA.TR06.expectedDimension d n r)))
    (hu : u ∈ c.chart.source) (hp : ∀ i, c.summands u i (q i) ≠ 0) :
    (fun y => NLA.TR06.orderedTensorFromPivotData q (NLA.TR06.chartPivotMap c q y))
      =ᶠ[𝓝 u] c.summands := by
  have hnear : ∀ᶠ y in 𝓝 u, ∀ i, c.summands y i (q i) ≠ 0 :=
    (NLA.TR06.chart_summands_contDiffAt c u hu).continuousAt.preimage_mem_nhds
      ((NLA.TR06.isOpen_orderedTensorPivotSet q).mem_nhds hp)
  filter_upwards [c.chart.open_source.mem_nhds hu,hnear] with y hy hpy
  funext i
  exact NLA.TR06.tensorFromPivotData_to (q i) (c.summands y i)
    ((c.decomposes y hy).1 i) (hpy i)

theorem chart_summand_derivative_decoder (c : NLA.TR06.SmoothDecompositionChart d n r)
    (q : Fin r → NLA.TR06.TensorIndex d n)
    (u w : EuclideanSpace ℝ (Fin (NLA.TR06.expectedDimension d n r)))
    (hu : u ∈ c.chart.source) (hp : ∀ i, c.summands u i (q i) ≠ 0) (i : Fin r) :
    fderiv ℝ (fun y => c.summands y i) u w =
      fderiv ℝ (NLA.TR06.tensorFromPivotData (q i))
        (NLA.TR06.chartPivotMap c q u i)
        ((fderiv ℝ (NLA.TR06.chartPivotMap c q) u w) i) := by
  have hmap := (NLA.TR06.chartPivotMap_contDiffAt c q u hu hp).differentiableAt one_ne_zero
  have hentry := (hasFDerivAt_apply (𝕜 := ℝ) i (NLA.TR06.chartPivotMap c q u)).comp u
    hmap.hasFDerivAt
  have hcomp := ((NLA.TR06.contDiff_tensorFromPivotData (q i) 1).differentiable
    one_ne_zero (NLA.TR06.chartPivotMap c q u i)).hasFDerivAt.comp u hentry
  have hlocal : (fun y => NLA.TR06.tensorFromPivotData (q i)
      (NLA.TR06.chartPivotMap c q y i)) =ᶠ[𝓝 u] fun y => c.summands y i :=
    (chart_decoder_eventuallyEq c q u hu hp).mono
      (fun y hy => congrArg (fun a => a i) hy)
  have heq := hlocal.fderiv_eq (𝕜 := ℝ)
  rw [← heq]
  exact congrArg (fun L : EuclideanSpace ℝ (Fin (NLA.TR06.expectedDimension d n r)) →L[ℝ]
    NLA.TR06.Tensor ℝ d n => L w) hcomp.fderiv

theorem chart_tangent_range (c : NLA.TR06.SmoothDecompositionChart d n r)
    (j₀ : Fin d) (u : EuclideanSpace ℝ (Fin (NLA.TR06.expectedDimension d n r)))
    (hu : u ∈ c.chart.source) (v : Fin r → NLA.TR06.Tensor ℝ d n) :
    (∀ i, NLA.Statements.TR06.RankOneTangent (c.summands u i) (v i)) ↔
      ∃ w : EuclideanSpace ℝ (Fin (NLA.TR06.expectedDimension d n r)),
        ∀ i, fderiv ℝ (fun y => c.summands y i) u w = v i := by
  classical
  have hq : ∀ i, ∃ q : NLA.TR06.TensorIndex d n, c.summands u i q ≠ 0 := by
    intro i
    by_contra! h
    exact ((c.decomposes u hu).1 i).1 (by ext q; exact h q)
  choose q hq using hq
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (NLA.TR06.expectedDimension d n r))) =
      Module.finrank ℝ (NLA.TR06.OrderedPivotData q) := by
    rw [finrank_euclideanSpace_fin,NLA.TR06.finrank_orderedPivotData]
  let L := (fderiv ℝ (NLA.TR06.chartPivotMap c q) u).toLinearMap.linearEquivOfInjective
    (NLA.TR06.chartPivotMap_injective_derivative c q u hu hq) hdim
  constructor
  · intro hv
    choose ξ hξ using fun i => rankOneTangent_has_pivot_preimage (q i)
      (c.summands u i) (v i) (hq i) (hv i)
    obtain ⟨w,hw⟩ := L.surjective ξ
    refine ⟨w,fun i => ?_⟩
    rw [chart_summand_derivative_decoder c q u w hu hq i]
    change fderiv ℝ (NLA.TR06.tensorFromPivotData (q i))
      (NLA.TR06.tensorToPivotData (q i) (c.summands u i)) ((L w) i) = v i
    rw [hw]
    exact hξ i
  · rintro ⟨w,hw⟩ i
    rw [← hw i,chart_summand_derivative_decoder c q u w hu hq i]
    have ht := rankOneTangent_decoder (q i) j₀
      (NLA.TR06.chartPivotMap c q u i) ((fderiv ℝ (NLA.TR06.chartPivotMap c q) u w) i)
    have heq : NLA.TR06.tensorFromPivotData (q i) (NLA.TR06.chartPivotMap c q u i) =
        c.summands u i := congrFun (chart_decoder_eventuallyEq c q u hu hq).self_of_nhds i
    rwa [heq] at ht

theorem chart_input_derivative_sum (c : NLA.TR06.SmoothDecompositionChart d n r)
    (u w : EuclideanSpace ℝ (Fin (NLA.TR06.expectedDimension d n r)))
    (hu : u ∈ c.chart.source) :
    fderiv ℝ (fun y => (c.chart y).val) u w =
      ∑ i, fderiv ℝ (fun y => c.summands y i) u w := by
  have hsum : HasFDerivAt (fun y => ∑ i, c.summands y i)
      (∑ i, fderiv ℝ (fun y => c.summands y i) u) u := by
    apply HasFDerivAt.fun_sum
    intro i _
    exact (((c.summands_smooth i).of_le (by simp)).contDiffAt
      (c.chart.open_source.mem_nhds hu)).differentiableAt one_ne_zero |>.hasFDerivAt
  have heq : (fun y => ∑ i, c.summands y i) =ᶠ[𝓝 u] fun y => (c.chart y).val := by
    filter_upwards [c.chart.open_source.mem_nhds hu] with y hy
    exact (c.decomposes y hy).2
  rw [← heq.fderiv_eq,hsum.fderiv]
  simp only [sum_apply]

theorem chart_regularDecomposition (c : NLA.TR06.SmoothDecompositionChart d n r)
    (j₀ : Fin d) (u : EuclideanSpace ℝ (Fin (NLA.TR06.expectedDimension d n r)))
    (hu : u ∈ c.chart.source) :
    NLA.Statements.TR06.RegularDecomposition (c.summands u) := by
  intro v hv hsum
  obtain ⟨w,hw⟩ := (chart_tangent_range c j₀ u hu v).mp hv
  have hz : fderiv ℝ (fun y => (c.chart y).val) u w = 0 := by
    rw [chart_input_derivative_sum c u w hu]
    simpa only [hw] using hsum
  have hwzero : w=0 := c.input_injective_derivative u hu (by simpa only [map_zero] using hz)
  intro i
  rw [← hw i,hwzero,map_zero]

theorem smoothRegular_subset_intrinsic (j₀ : Fin d) :
    NLA.TR06.smoothRegularSet d n r ⊆
      {A | NLA.Statements.TR06.SmoothIdentifiable n r A} := by
  rintro A ⟨c,u,hu,rfl⟩
  refine ⟨(exactRank_iff _).mpr (c.chart u).property.1,
    (identifiable_iff _).mpr (c.chart u).property.2,c.summands u,
    (decomposes_iff _ _).mpr (c.decomposes u hu),chart_regularDecomposition c j₀ u hu⟩

theorem chart_output_derivative (c : NLA.TR06.SmoothDecompositionChart d n r)
    (u w : EuclideanSpace ℝ (Fin (NLA.TR06.expectedDimension d n r)))
    (hu : u ∈ c.chart.source) :
    fderiv ℝ (fun y => NLA.TR06.normalizedTuple (c.summands y)) u w =
      NLA.Statements.TR06.AngularProductVariation (c.summands u)
        (fun i => fderiv ℝ (fun y => c.summands y i) u w) := by
  apply fderiv_normalizedTuple_apply
  · intro i
    exact (((c.summands_smooth i).of_le (by simp)).contDiffAt
      (c.chart.open_source.mem_nhds hu)).differentiableAt one_ne_zero
  · exact fun i => ((c.decomposes u hu).1 i).1

#assert_trust kernel chart_decoder_eventuallyEq
#assert_trust kernel chart_summand_derivative_decoder
#assert_trust kernel chart_tangent_range
#assert_trust kernel chart_input_derivative_sum
#assert_trust kernel chart_regularDecomposition
#assert_trust kernel smoothRegular_subset_intrinsic
#assert_trust kernel chart_output_derivative
#print axioms chart_tangent_range
#print axioms smoothRegular_subset_intrinsic
#print axioms chart_output_derivative
end NLA.Proofs.TR06.Model
