import NLA.FR05.SmallBall.SourceRowSmallBall
import NLA.FR05.SmallBall.RowDistanceProbability
open MeasureTheory WithLp
open scoped ENNReal RealInnerProductSpace
namespace NLA.FR05
theorem measurable_sourceJacobianRow {n : ℕ} :
    Measurable (fun p : SourcePlantedCoordinates n ↦ fun j : SourceJacobianCoordinate n ↦
      sourceRowJacobianLinear (sourceCoordinatesToPlantedRowOrDefault p) (Pi.single j (1 : ℝ) : SourceJacobianVector n)) := by
  apply measurable_pi_lambda
  intro j
  simp only [sourceRowJacobianLinear, LinearMap.coe_mk, AddHom.coe_mk,
    sourceCoordinatesToPlantedRowOrDefault]
  have hs : MeasurableSet {p : SourcePlantedCoordinates n |
      0 < p.1.1 ∧ |p.1.2.1| ≤ 1} := by measurability
  have he : (fun p : SourcePlantedCoordinates n ↦
      sourceRowJacobianForm
        (if h : 0 < p.1.1 ∧ |p.1.2.1| ≤ 1 then
          sourceCoordinatesToPlantedRow p h.1 h.2 else
          { radial := 1, imbalance := 0, phaseOne := 0, phaseTwo := 0, tail := 0,
            radial_pos := zero_lt_one, imbalance_le_one := by norm_num })
        ((Pi.single j (1 : ℝ) : SourceJacobianVector n) .sigma) ((Pi.single j (1 : ℝ) : SourceJacobianVector n) .beta) ((Pi.single j (1 : ℝ) : SourceJacobianVector n) .gamma)
        (sourceJacobianP (Pi.single j (1 : ℝ) : SourceJacobianVector n)) (sourceJacobianQ (Pi.single j (1 : ℝ) : SourceJacobianVector n))) =
      fun p ↦ if 0 < p.1.1 ∧ |p.1.2.1| ≤ 1 then
        (Pi.single j (1 : ℝ) : SourceJacobianVector n) .sigma / 2 +
          (Pi.single j (1 : ℝ) : SourceJacobianVector n) .beta * Real.cos (p.1.2.2.2 - p.1.2.2.1) -
          (Pi.single j (1 : ℝ) : SourceJacobianVector n) .gamma * Real.sin (p.1.2.2.2 - p.1.2.2.1) +
          Real.sqrt (2 / p.1.1) *
            (star ((Complex.exp ((-p.1.2.2.1 : ℂ) * Complex.I)) • p.2) ⬝ᵥ
              (sourceJacobianP (Pi.single j (1 : ℝ) : SourceJacobianVector n) +
                Complex.exp (((p.1.2.2.2 - p.1.2.2.1 : ℝ) : ℂ) * Complex.I) •
                  sourceJacobianQ (Pi.single j (1 : ℝ) : SourceJacobianVector n))).re
      else sourceRowJacobianForm
        { radial := 1, imbalance := 0, phaseOne := 0, phaseTwo := 0, tail := 0,
          radial_pos := zero_lt_one, imbalance_le_one := by norm_num }
        ((Pi.single j (1 : ℝ) : SourceJacobianVector n) .sigma) ((Pi.single j (1 : ℝ) : SourceJacobianVector n) .beta) ((Pi.single j (1 : ℝ) : SourceJacobianVector n) .gamma)
        (sourceJacobianP (Pi.single j (1 : ℝ) : SourceJacobianVector n)) (sourceJacobianQ (Pi.single j (1 : ℝ) : SourceJacobianVector n)) := by
    funext p
    split <;> simp_all [sourceRowJacobianForm, sourceCoordinatesToPlantedRow,
      phaseGap, phaseNormalizedTail]
  rw [he]
  apply Measurable.ite hs _ measurable_const
  unfold dotProduct
  fun_prop

theorem sourceJacobianRow_inner {n : ℕ} (p : SourcePlantedCoordinates n)
    (v : EuclideanSpace ℝ (SourceJacobianCoordinate n)) :
    inner ℝ v (toLp 2 (fun j ↦
      sourceRowJacobianLinear (sourceCoordinatesToPlantedRowOrDefault p) (Pi.single j (1 : ℝ) : SourceJacobianVector n))) =
      sourceRowJacobianForm (sourceCoordinatesToPlantedRowOrDefault p)
        ((ofLp v) .sigma) ((ofLp v) .beta) ((ofLp v) .gamma)
        (sourceJacobianP (ofLp v)) (sourceJacobianQ (ofLp v)) := by
  change _ = sourceRowJacobianLinear (sourceCoordinatesToPlantedRowOrDefault p) (ofLp v)
  rw [sourceRowJacobianLinear_eq_sum_coordinates]
  simp [PiLp.inner_apply, mul_comm]

theorem iidSourceCoordinateLaw_rowNearSpan_le {M m n : ℕ} (hM : 1 ≤ M)
    (e : SourceJacobianCoordinate n ≃ Fin m) (i : SourceJacobianCoordinate n)
    (u t : ℝ) (hu : 0 ≤ u) (ht : 0 < t) (hscale : 2 * u ≤ t) :
    iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n
      {sample | rowNearSpan (sourceJacobianMatrixFromCoordinates e sample) i u} ≤
      max (sourceTailSmallBallBound M u t) (sourceNonTailSmallBallBound u t) := by
  let := isProbabilityMeasure_sourceCoordinateLaw (δ := sourceDelta M) sourceEta_pos.le sourceEta_lt_one
    (sourceEpsilon_pos M hM) n
  apply iid_rowNearSpan_reindex_le e _ _ measurable_sourceJacobianRow i u _
  intro v hv
  have hunit : sourceJacobianEnergy (ofLp v) = 1 := by
    rw [sourceJacobianEnergy_ofLp_eq_norm_sq, hv, one_pow]
  have hh := sourceCoordinateLaw_sourceM_sourceJacobianRowSmallBall_le_max
    hM (ofLp v) hunit u t hu ht hscale
  simpa only [sourceJacobianRow_inner, sourceRowJacobianSmallBallEvent] using hh

theorem iidSourceCoordinateLaw_leastGain_failure_le {M m n : ℕ} (hM : 1 ≤ M)
    (e : SourceJacobianCoordinate n ≃ Fin m) {κ t : ℝ}
    (hκ : 0 < κ) (ht : 0 < t) (hscale : 2 * ((m : ℝ) * κ) ≤ t) :
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n).real
      {sample | ¬ HasEuclideanLowerBound (sourceJacobianMatrixFromCoordinates e sample) κ} ≤
      (m : ℝ) *
        (max (sourceTailSmallBallBound M ((m : ℝ) * κ) t)
          (sourceNonTailSmallBallBound ((m : ℝ) * κ) t)).toReal := by
  let μ := iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n
  let : IsProbabilityMeasure μ := isProbabilityMeasure_iidSourceCoordinateLaw
    sourceEta_pos.le sourceEta_lt_one (sourceEpsilon_pos M hM) m n
  have hc : Fintype.card (SourceJacobianCoordinate n) = m := by
    simpa using Fintype.card_congr e
  have hh := measureReal_not_hasEuclideanLowerBound_le_card_mul_of_rowEvent_bound
    (p := (max (sourceTailSmallBallBound M ((m : ℝ) * κ) t)
      (sourceNonTailSmallBallBound ((m : ℝ) * κ) t)).toReal)
    μ (sourceJacobianMatrixFromCoordinates e) hκ
  rw [hc] at hh
  apply hh
  intro i
  apply (measureReal_mono (fun _ h ↦ rowSpanDistanceBad_implies_rowNearSpan h)
    (measure_lt_top μ _).ne).trans
  apply ENNReal.toReal_mono
  · unfold sourceTailSmallBallBound sourceNonTailSmallBallBound
    finiteness
  · exact iidSourceCoordinateLaw_rowNearSpan_le hM e i ((m : ℝ) * κ) t
      (by positivity) ht hscale

end NLA.FR05
