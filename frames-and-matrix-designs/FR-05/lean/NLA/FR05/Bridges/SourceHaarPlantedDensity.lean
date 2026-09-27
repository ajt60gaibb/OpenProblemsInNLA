/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Identification of the Haar-mixed planted sampler with likelihood (3.5)
relative to the original standard complex Gaussian frame law.
-/
import NLA.FR05.Bridges.SourcePlantedFrameDensity
import NLA.FR05.Planted.PlantedHaarFailure
import NLA.FR05.Overlap.HaarCorner

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace NLA.FR05


instance sourceUnitaryLaw_isInvInvariant (n : ℕ) :
    (sourceUnitaryLaw n).IsInvInvariant where
  inv_eq_self := by
    let : IsProbabilityMeasure (sourceUnitaryLaw n).inv :=
      Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
    have he := Measure.isMulLeftInvariant_eq_smul_of_innerRegular
      (sourceUnitaryLaw n).inv (sourceUnitaryLaw n)
    have hc := congrArg (fun μ : Measure (SourceUnitary n) ↦ μ Set.univ) he
    have hfactor : Measure.haarScalarFactor (sourceUnitaryLaw n).inv (sourceUnitaryLaw n) = 1 := by
      simpa using hc.symm
    simpa only [hfactor, one_smul] using he

theorem standardComplexGaussianFrame_map_mul_unitary {m d : ℕ} (U : SourceUnitary d) :
    (standardComplexGaussianFrame m d).map (fun A ↦ A * U.val) =
      standardComplexGaussianFrame m d := by
  have hrow : (standardComplexGaussianTail d).map (fun x ↦ x ᵥ* U.val) =
      standardComplexGaussianTail d := by
    convert standardComplexGaussianTail_map_unitary U.val
      (Matrix.UnitaryGroup.star_mul_self U) using 2
    funext x
    ext j
    simp [vecMul, mulVec, dotProduct, conjTranspose_apply, mul_comm]
  rw [standardComplexGaussianFrame_eq_pi]
  change (Measure.pi (fun _ : Fin m ↦ standardComplexGaussianTail d)).map
    (fun A i ↦ A i ᵥ* U.val) = _
  rw [Measure.pi_map_pi (f := fun _ : Fin m ↦ fun x : Signal d ↦ x ᵥ* U.val)
    (fun _ ↦ by fun_prop)]
  simp_rw [hrow]

theorem sourceHead_star_frame_mul {m n : ℕ} (U : SourceUnitary (n + 2))
    (A : Frame m (n + 2)) (i : Fin m) :
    sourceHead (star ((A * U.val) i)) = sourceProjectedRow (by lia) U (A i) := by
  ext j
  simp [sourceHead, sourceProjectedRow, sourceTwoFrame, Matrix.mul_apply,
    mul_comm, Fin.castLE]

/-- The likelihood for one fixed orientation, before Haar averaging. -/
def sourceOrientedPlantedDensity (M : ℕ) {m n : ℕ}
    (U : SourceUnitary (n + 2)) (A : Frame m (n + 2)) : ℝ :=
  ∏ i, sourcePlantedDensity M (sourceProjectedRow (by lia) U (A i))

@[fun_prop] theorem measurable_sourceOrientedPlantedDensity (M : ℕ) (m n : ℕ) :
    Measurable (fun p : SourceUnitary (n + 2) × Frame m (n + 2) ↦
      sourceOrientedPlantedDensity M p.1 p.2) := by
  apply Finset.measurable_prod
  intro i _
  exact (measurable_sourcePlantedDensity M).comp
    ((continuous_sourceProjectedRow (by lia)).measurable.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))

theorem sourceOrientedPlantedDensity_eq (M : ℕ) {m n : ℕ}
    (U : SourceUnitary (n + 2)) (A : Frame m (n + 2)) :
    sourceOrientedPlantedDensity M U A =
      ∏ i, sourcePlantedDensity M (sourceHead (star ((A * U.val) i))) := by
  simp only [sourceOrientedPlantedDensity, sourceHead_star_frame_mul]

/-- A fixed unitary rotation of the planted sampler has the expected
projected-row density relative to the same Gaussian frame law. -/
theorem iidSourcePlantedFrameLaw_map_unitary_eq_withDensity {M m n : ℕ}
    (hM : 1 ≤ M) (U : SourceUnitary (n + 2)) :
    (iidSourcePlantedFrameLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n).map
      (fun A ↦ A * (star U).val) =
      (standardComplexGaussianFrame m (n + 2)).withDensity
        (fun A ↦ ENNReal.ofReal (sourceOrientedPlantedDensity M U A)) := by
  rw [iidSourcePlantedFrameLaw_eq_withDensity hM]
  have he : (fun A : Frame m (n + 2) ↦ ENNReal.ofReal
      (∏ i, sourcePlantedDensity M (sourceHead (star (A i))))) =
      fun A ↦ ENNReal.ofReal (sourceOrientedPlantedDensity M U (A * (star U).val)) := by
    funext A
    rw [sourceOrientedPlantedDensity_eq, Matrix.mul_assoc,
      show (star U).val * U.val = 1 from Matrix.UnitaryGroup.star_mul_self U,
      Matrix.mul_one]
  rw [he, map_withDensity_comp _ (fun A : Frame m (n + 2) ↦ A * (star U).val)
      (show Measurable (fun A : Frame m (n + 2) ↦ A * (star U).val) from
        measurable_frame_mul_unitary.comp (measurable_const.prodMk measurable_id))
      (fun A ↦ ENNReal.ofReal (sourceOrientedPlantedDensity M U A))
      (((measurable_sourceOrientedPlantedDensity M m n).comp
        (measurable_const.prodMk measurable_id)).ennreal_ofReal),
    standardComplexGaussianFrame_map_mul_unitary]

theorem sourceOrientedPlantedDensity_nonneg (M : ℕ) {m n : ℕ}
    (U : SourceUnitary (n + 2)) (A : Frame m (n + 2)) :
    0 ≤ sourceOrientedPlantedDensity M U A :=
  Finset.prod_nonneg fun _ _ ↦ sourcePlantedDensity_nonneg M _

theorem integrable_sourceOrientedPlantedDensity {M m n : ℕ} (hM : 1 ≤ M)
    (A : Frame m (n + 2)) :
    Integrable (fun U ↦ sourceOrientedPlantedDensity M U A) (sourceUnitaryLaw (n + 2)) := by
  have hmeas : Measurable (fun U : SourceUnitary (n + 2) ↦
      sourceOrientedPlantedDensity M U A) := by
    apply Finset.measurable_prod
    intro i _
    exact (measurable_sourcePlantedDensity M).comp
      ((continuous_sourceProjectedRow (by lia)).measurable.comp
        (measurable_id.prodMk measurable_const))
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    ((Real.exp 1 * (M : ℝ) ^ 52) ^ m)
  filter_upwards with U
  rw [Real.norm_eq_abs, abs_of_nonneg (sourceOrientedPlantedDensity_nonneg M U A)]
  calc
    _ ≤ ∏ _ : Fin m, (Real.exp 1 * (M : ℝ) ^ 52) :=
      Finset.prod_le_prod (fun i _ ↦ sourcePlantedDensity_nonneg M _)
        (fun i _ ↦ sourcePlantedDensity_le hM _)
    _ = _ := by simp

/-- Haar averaging the generative planted frame agrees with Haar averaging
its projected-row likelihood. -/
theorem iidSourcePlantedFrameLaw_haar_eq_withDensity {M m n : ℕ} (hM : 1 ≤ M) :
    ((sourceUnitaryLaw (n + 2)).prod
      (iidSourcePlantedFrameLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n)).map
        (fun p ↦ p.2 * p.1.val) =
      (standardComplexGaussianFrame m (n + 2)).withDensity
        (fun A ↦ ENNReal.ofReal (∫ U, sourceOrientedPlantedDensity M U A
          ∂sourceUnitaryLaw (n + 2))) := by
  let ν := iidSourcePlantedFrameLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n
  have : IsProbabilityMeasure ν := isProbabilityMeasure_iidSourcePlantedFrameLaw
    sourceEta_pos.le sourceEta_lt_one (sourceEpsilon_pos M hM) m n
  exact Measure.map_prod_eq_withDensity_of_inv (sourceUnitaryLaw (n + 2))
    (standardComplexGaussianFrame m (n + 2)) ν
    (fun U A ↦ A * U.val) measurable_frame_mul_unitary
    (sourceOrientedPlantedDensity M) (measurable_sourceOrientedPlantedDensity M m n)
    (sourceOrientedPlantedDensity_nonneg M) (integrable_sourceOrientedPlantedDensity hM)
    (iidSourcePlantedFrameLaw_map_unitary_eq_withDensity hM)

/-- Relabel the source's `M - 2 + 2` columns by the original ambient dimension. -/
def sourceFrameAtDimension {M : ℕ} (hM : 2 ≤ M)
    (A : Frame (sourceRowCount M) (sourceTailDimension M + 2)) :
    Frame (sourceRowCount M) M :=
  fun i j ↦ A i (Fin.cast (sourceTailDimension_add_two hM).symm j)

/-- The actual Haar-mixed planted sampler has likelihood (3.5) relative to the
original standard complex Gaussian frame law. -/
theorem sourceHaarPlantedFrameLawAt_eq_likelihood {M : ℕ} (hM : 2 ≤ M) :
    (sourceHaarPlantedFrameLawAt M).map (sourceFrameAtDimension hM) =
      (standardComplexGaussianFrame (sourceRowCount M) M).withDensity
        (fun A ↦ ENNReal.ofReal (sourcePlantedLikelihood hM A)) := by
  have transport (M n : ℕ) (hM : 2 ≤ M) (hd : n + 2 = M) :
      (((sourceUnitaryLaw (n + 2)).prod
        (iidSourcePlantedFrameLaw sourceEta (sourceDelta M) (sourceEpsilon M)
          (sourceRowCount M) n)).map (fun p ↦ p.2 * p.1.val)).map
          (fun A : Frame (sourceRowCount M) (n + 2) ↦
            fun i j ↦ A i (Fin.cast hd.symm j)) =
        (standardComplexGaussianFrame (sourceRowCount M) M).withDensity
          (fun A ↦ ENNReal.ofReal (sourcePlantedLikelihood hM A)) := by
    subst M
    change Measure.map id _ = _
    rw [Measure.map_id]
    exact iidSourcePlantedFrameLaw_haar_eq_withDensity (by lia)
  exact transport M (sourceTailDimension M) hM (sourceTailDimension_add_two hM)

end NLA.FR05
