import NLA.IE06.GaussianAdaptiveFuture
import NLA.IE06.GaussianFutureSmoothing
import NLA.IE06.GaussianSpectralBase
import NLA.IE06.TruncatedInverse
import NLA.IE06.SpectralMeasurability
import NLA.IE06.GaussianPrefixDecomposition

/-! The intrinsic one-stage event for the reviewed B1+B2 assembly. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace NLA.IE06.GaussianStageSmoothing
open GaussianNull GaussianQuadratic GaussianPivotConditioning GaussianColumnSplit GaussianCoordinates
open GaussianSpectralBase TruncatedInverse EliminationSmoothing PivotFiltration

local instance matrixMeasurable (a b : ℕ) : MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin a → Fin b → ℝ))

theorem block_measurable {n t : ℕ} (ht : t ≤ n) : Measurable (block ht) := by
  apply measurable_matrix_entries
  intro i j
  have hp := measurable_pivotOrder_coordinate ht i
  have he : Measurable (fun p : Mat n × Fin n => p.1 p.2 (Fin.castLE ht j)) :=
    measurable_from_prod_countable_left (fun k => by fun_prop)
  exact he.comp (measurable_id.prodMk hp)

theorem sigmaInvSum_measurable (t r : ℕ) :
    Measurable (fun T : Mat t => sigmaInvSum (Matrix.of T) r) := by
  unfold sigmaInvSum
  apply Finset.measurable_sum
  intro i _
  exact ((SpectralMeasurability.measurable_singularValue i.val).inv).pow_const 2

theorem block_restore_future {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n)
    (z : Mat t × (RemainingRows π → Fin t → ℝ)) (W V : FutureBlock n t) :
    block ht (restore ht π (z,W)) = block ht (restore ht π (z,V)) := by
  have ho := pivotOrder_columns_congr ht (restore ht π (z,W)) (restore ht π (z,V))
    (restore_prefix_congr ht π z W V)
  unfold block
  rw [ho]
  funext i j
  exact restore_prefix_congr ht π z W V _ _ j.isLt

def stageEvent {n t : ℕ} (ht : t ≤ n) (r : ℕ) (τ x : ℝ) : Set (Mat n) :=
  {A | sigmaInvSum (block ht A) r ≤ τ} ∩
    GaussianFutureSmoothing.badEvent n (t+4*r)
      (GaussianFutureSmoothing.threshold (4*r) r (Real.sqrt (1+(2+4*x)*τ)) x)

theorem stageEvent_measurable {n t : ℕ} (ht : t ≤ n) (r : ℕ) (τ x : ℝ) :
    MeasurableSet (stageEvent ht r τ x) :=
  (measurableSet_le ((sigmaInvSum_measurable t r).comp (block_measurable ht)) measurable_const).inter
    (GaussianFutureSmoothing.badEvent_measurable _ _ _)

/-- A bounded future probability may be integrated with one exceptional set.
All exceptional probabilities remain explicit in the resulting bound. -/
theorem lintegral_le_exception_add {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ≥0∞)
    (S : Set Ω) (hS : MeasurableSet S) (c : ℝ≥0∞)
    (h1 : ∀ z, f z ≤ 1) (hc : ∀ᵐ z ∂μ, z ∉ S → f z ≤ c) :
    (∫⁻ z, f z ∂μ) ≤ μ S+c := by
  have hb : ∀ᵐ z ∂μ, f z ≤ S.indicator 1 z+c := by
    filter_upwards [hc] with z hz
    by_cases h : z ∈ S
    · simpa only [Set.indicator_of_mem h,Pi.one_apply] using
        (h1 z).trans (le_add_of_nonneg_right zero_le : (1:ℝ≥0∞) ≤ 1+c)
    · simpa only [Set.indicator_of_notMem h,zero_add] using hz h
  calc
    _ ≤ ∫⁻ z, S.indicator 1 z+c ∂μ := lintegral_mono_ae hb
    _ = μ S+c := by
      rw [lintegral_add_left (measurable_one.indicator hS),lintegral_indicator_one hS]
      simp

/-- Actual stage B1+B2, with the inverse-sum guard at the exposed prefix
and no conditioning on the success of any later pivot. -/
theorem stage_tail {n t r : ℕ} (h : t+4*r ≤ n) (hr1 : 1 ≤ r) (hrt : r < t)
    {τ x : ℝ} (_hτ0 : 0 ≤ τ) (hx : 0 < x) :
    gaussianMatrix n (stageEvent (by omega : t ≤ n) r τ x) ≤
      (2*(n:ℝ≥0∞)+1)*ENNReal.ofReal (Real.exp (-x)) := by
  let ht : t ≤ n := by omega
  let K := GaussianFutureSmoothing.threshold (4*r) r (Real.sqrt (1+(2+4*x)*τ)) x
  apply GaussianAdaptiveFuture.event_le ht (stageEvent ht r τ x) (stageEvent_measurable ht r τ x)
  intro π T hg
  let ν := GaussianPrefixDecomposition.fiberLaw π T
  let f := fun Z : RemainingRows π → Fin t → ℝ =>
    futureLaw n t {W | restore ht π ((T,Z),W) ∈ stageEvent ht r τ x}
  change (∫⁻ Z, f Z ∂ν) ≤ _
  let _ := GaussianRestriction.restrictedGaussian_probability (ne_of_gt (truncationBody_mass_pos T))
  let _ : IsProbabilityMeasure ν := by dsimp [ν,GaussianPrefixDecomposition.fiberLaw]; infer_instance
  by_cases hτ : sigmaInvSum T r ≤ τ
  · obtain ⟨R,H,V,_hV,_hT,_hF,hQ,hE,hbad⟩ :=
      GaussianPrefixDecomposition.exists_prefix_decomposition ht π T hg hr1 hrt hx hτ
    let S := {Z : RemainingRows π → Fin t → ℝ | ∃ i : Fin n,
      Real.sqrt (1+(2+4*x)*τ) < rowNorm
        (SelectedBlockTruncation.retainedRows ht (GaussianPrefixDecomposition.prefixInput ht π T Z) R) i}
    have hS : MeasurableSet S := GaussianPrefixDecomposition.measurableSet_bad_retainedRows ht π T R _
    have hc : ∀ᵐ Z ∂ν, Z ∉ S → f Z ≤ ((n:ℝ≥0∞)+1)*ENNReal.ofReal (Real.exp (-x)) := by
      filter_upwards [hE] with Z hZ
      intro hnot
      have hcap : ∀ i, rowNorm (SelectedBlockTruncation.retainedRows ht
          (GaussianPrefixDecomposition.prefixInput ht π T Z) R) i ≤ Real.sqrt (1+(2+4*x)*τ) := by
        intro i
        exact le_of_not_gt (fun hi => hnot ⟨i,hi⟩)
      apply (measure_mono (show {W : FutureBlock n t |
        restore ht π ((T,Z),W) ∈ stageEvent ht r τ x} ⊆
        {W | restore ht π ((T,Z),W) ∈ GaussianFutureSmoothing.badEvent n (t+4*r) K}
          from fun _ hW => hW.2)).trans
      exact GaussianFutureSmoothing.fixed_prefix_tail h π (T,Z)
        (SelectedBlockTruncation.retainedRows ht (GaussianPrefixDecomposition.prefixInput ht π T Z) R)
        (SelectedBlockTruncation.discardedRows ht (GaussianPrefixDecomposition.prefixInput ht π T Z) H)
        (SelectedBlockTruncation.coordinateEmbedding π * V) hZ.2.2 hQ (by omega) le_rfl
        (by omega) (Real.sqrt_nonneg _) hcap x hx
    have hb := lintegral_le_exception_add ν f S hS
      (((n:ℝ≥0∞)+1)*ENNReal.ofReal (Real.exp (-x))) (fun _ => prob_le_one) hc
    calc
      _ ≤ ν S+((n:ℝ≥0∞)+1)*ENNReal.ofReal (Real.exp (-x)) := hb
      _ ≤ (n:ℝ≥0∞)*ENNReal.ofReal (Real.exp (-x))+
          ((n:ℝ≥0∞)+1)*ENNReal.ofReal (Real.exp (-x)) := add_le_add hbad le_rfl
      _ = _ := by ring
  · have hf : ∀ᵐ Z ∂ν, f Z = 0 := by
      filter_upwards [GaussianPrefixDecomposition.prefix_data_ae ht π T hg] with Z hZ
      have hz : ∀ W : FutureBlock n t, block ht (restore ht π ((T,Z),W)) = T := by
        intro W
        exact (block_restore_future ht π (T,Z) W 0).trans hZ.2.1
      have he : {W : FutureBlock n t | restore ht π ((T,Z),W) ∈ stageEvent ht r τ x} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro W hW
        have hs := hW.1
        change sigmaInvSum (block ht (restore ht π ((T,Z),W))) r ≤ τ at hs
        rw [hz W] at hs
        exact hτ hs
      dsimp [f]
      rw [he,measure_empty]
    rw [lintegral_congr_ae hf,lintegral_zero]
    exact zero_le

#assert_trust kernel matrixMeasurable
#assert_trust kernel block_measurable
#assert_trust kernel sigmaInvSum_measurable
#assert_trust kernel block_restore_future
#assert_trust kernel stageEvent
#assert_trust kernel stageEvent_measurable
#assert_trust kernel lintegral_le_exception_add
#assert_trust kernel stage_tail
#print axioms lintegral_le_exception_add
#print axioms stage_tail
end NLA.IE06.GaussianStageSmoothing
