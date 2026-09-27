import NLA.FR05.Planted.SourceHighProbability
import NLA.FR05.Planted.SourceLocalControl
import NLA.FR05.Geometry.InjectivityMeasurable

set_option autoImplicit false
noncomputable section
open MeasureTheory WithLp
namespace NLA.FR05

theorem sourceNewtonGood_not_injective {M : ℕ} (hM : 8192 ≤ M)
    (sample : Fin (sourceRowCount M) → SourcePlantedCoordinates (sourceTailDimension M))
    (hgood : SourceNewtonGood M (by lia) sample) :
    ¬ PhaseRetrievalInjective (plantedFrame (sourceRowsFromCoordinates sample)) := by
  let e := sourceJacobianCoordinateEquivSourceRows M (by lia)
  obtain ⟨hR, hR1, hres, hlip⟩ := sourceNewton_calibration hM
  have hseed := sourceEquation_seed_le (by lia : 2 ≤ M) e sample hgood.1 hgood.2.2
  obtain ⟨x, hx, hzero⟩ := exists_zero_of_local_linear_control
    (sourceEquationEuclidean e sample)
    (euclideanMap (sourceJacobianMatrixAt M (by lia) sample))
    (sourceKappa_pos M (by lia)) hR hgood.2.1
    (show 2 * ‖sourceEquationEuclidean e sample 0‖ ≤
        sourceKappa M * sourceNewtonRadius M by linarith)
    (by
      intro x y hx hy
      exact (sourceEquation_frozen_difference_le (by lia : 2 ≤ M) e sample
        hgood.1 hgood.2.2 x y hR hx hy).trans
        (mul_le_mul_of_nonneg_right hlip (norm_nonneg _)))
  let θ := sourceFactorDecode x
  apply plantedFrame_not_phaseRetrievalInjective_of_equations_eq_zero
    (sourceRowsFromCoordinates sample) θ.1 θ.2.1 θ.2.2.1 θ.2.2.2
  · have hs := abs_sourceJacobianCoordinate_le_euclideanNorm (ofLp x) .sigma
    have hs' : |θ.1| ≤ ‖x‖ := by simpa [θ, sourceFactorDecode] using hs
    exact hs'.trans (hx.trans hR1)
  · intro i
    have hi := congr_fun (congrArg ofLp hzero) (e.symm i)
    change plantedEquationMap (sourceRowsFromCoordinates sample)
      (sourceFactorDecode x) (e (e.symm i)) = 0 at hi
    simpa only [plantedEquationMap, Equiv.apply_symm_apply] using hi

theorem sourcePlantedFrameLaw_injective_le_bad {M : ℕ} (hM : 8192 ≤ M) :
    (sourcePlantedFrameLawAt M).real {A | PhaseRetrievalInjective A} ≤
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M)
        (sourceRowCount M) (sourceTailDimension M)).real
        {sample | ¬ SourceNewtonGood M (by lia) sample} := by
  let μ := iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M)
    (sourceRowCount M) (sourceTailDimension M)
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_iidSourceCoordinateLaw
    sourceEta_pos.le sourceEta_lt_one (sourceEpsilon_pos M (by lia)) _ _
  have hm : Measurable (sourceFrameFromCoordinates
      (m := sourceRowCount M) (n := sourceTailDimension M)) :=
    measurable_frameFromPlantedColumns.comp measurable_sourceColumnsFromCoordinates
  have he := ae_sourceFrameFromCoordinates_eq_plantedFrameAt (show 1 ≤ M by lia)
  have hsub :
      {sample | PhaseRetrievalInjective (sourceFrameFromCoordinates sample)} ≤ᵐ[μ]
      {sample | ¬ SourceNewtonGood M (by lia) sample} := by
    filter_upwards [he] with sample heq
    intro hinj hgood
    change PhaseRetrievalInjective (sourceFrameFromCoordinates sample) at hinj
    rw [heq] at hinj
    exact sourceNewtonGood_not_injective hM sample hgood hinj
  have hs : MeasurableSet {A : Frame (sourceRowCount M) (sourceTailDimension M + 2) |
      PhaseRetrievalInjective A} := measurableSet_phaseRetrievalInjective _ _
  have hmap := Measure.map_apply (μ := μ) hm hs
  unfold sourcePlantedFrameLawAt
  rw [iidSourcePlantedFrameLaw_eq_coordinatesMap _ _ sourceEta_pos.le
    sourceEta_lt_one (sourceEpsilon_pos M (by lia)), Measure.real_def]
  change ((μ.map sourceFrameFromCoordinates) _).toReal ≤ μ.real _
  rw [hmap]
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)

/-- Proposition 3.1 for the actual iid planted-frame law. -/
theorem proposition_3_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, 2 ≤ D ∧ ∀ M : ℕ, D ≤ M →
      (sourcePlantedFrameLawAt M).real {A | PhaseRetrievalInjective A} ≤
        C / (M : ℝ) ^ 2 := by
  obtain ⟨D, _, hD⟩ := sourceNewtonGood_failure_order
  refine ⟨113, by norm_num, max D 8192, by lia, fun M hM ↦ ?_⟩
  exact (sourcePlantedFrameLaw_injective_le_bad
    ((le_max_right D 8192).trans hM)).trans
    (hD M (by lia) ((le_max_left D 8192).trans hM))
end NLA.FR05
