import NLA.FR05.Overlap.HaarColumnConditioning
import NLA.FR05.Gaussian.ComplexVectorDensity
import NLA.FR05.Overlap.OverlapCholesky
import NLA.FR05.Overlap.Spectrum

/-!
# Rank-one sphere geometry and sequential sphere laws

The sections develop `RankOneSphereGeometry`, `SequentialSphereLaw`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section RankOneSphereGeometry

set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

def sphereComplementFirst (z : Signal 2) : ℝ := 1 - Complex.normSq (z 0)
def sphereComplementDet (z : Signal 2) : ℝ := 1 - signalEnergy z
def sphereComplementSecond (z : Signal 2) : ℝ :=
  sphereComplementDet z / sphereComplementFirst z
def sphereComplementSlope (z : Signal 2) : ℂ :=
  -(z 1 * star (z 0)) / (sphereComplementFirst z : ℂ)
def sphereComplementFactor (z : Signal 2) : SourceOverlapMatrix :=
  !![(Real.sqrt (sphereComplementFirst z) : ℂ), 0;
    sphereComplementSlope z * (Real.sqrt (sphereComplementFirst z) : ℂ),
    (Real.sqrt (sphereComplementSecond z) : ℂ)]

theorem sphereComplementFirst_pos {z : Signal 2} (hz : signalEnergy z < 1) :
    0 < sphereComplementFirst z := by
  simp only [signalEnergy, squaredEuclideanNorm, Fin.sum_univ_two] at hz
  unfold sphereComplementFirst
  linarith [Complex.normSq_nonneg (z 1)]

theorem sphereComplementDet_pos {z : Signal 2} (hz : signalEnergy z < 1) :
    0 < sphereComplementDet z := sub_pos.mpr hz

theorem sphereComplementSecond_pos {z : Signal 2} (hz : signalEnergy z < 1) :
    0 < sphereComplementSecond z :=
  div_pos (sphereComplementDet_pos hz) (sphereComplementFirst_pos hz)

theorem sphereComplementFactor_mulVec (z w : Signal 2) :
    sphereComplementFactor z *ᵥ w =
      triangularGaussian (sphereComplementFirst z) (sphereComplementSecond z)
        (sphereComplementSlope z) 0 w := by
  ext i
  fin_cases i <;> simp [sphereComplementFactor, triangularGaussian, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, Complex.real_smul]
  all_goals ring

theorem sphereComplementFactor_gram {z : Signal 2} (hz : signalEnergy z < 1) :
    sphereComplementFactor z * (sphereComplementFactor z)ᴴ =
      1 - Matrix.vecMulVec z (star z) := by
  let K : SourceOverlapMatrix := !![star (z 0), star (z 1); 0, 0]
  have hF : overlapFrobeniusSq K = signalEnergy z := by
    simp [K, overlapFrobeniusSq, signalEnergy, squaredEuclideanNorm, Fin.sum_univ_two]
  have hK : overlapOperatorNorm K < 1 := by
    have h := overlapOperatorNorm_sq_le_frobenius K
    rw [hF] at h
    nlinarith [overlapOperatorNorm_nonneg K]
  have he : overlapCholesky K = sphereComplementFactor z := by
    have hd : overlapDeterminant K = sphereComplementDet z := by
      rw [overlapDeterminant_identity, hF]
      simp [K, Matrix.det_fin_two, sphereComplementDet]
    have ha : overlapCholeskyFirst K = sphereComplementFirst z := by
      simp [overlapCholeskyFirst, overlapColumnEnergy, K,
        sphereComplementFirst]
    have hc : overlapCholeskySlope K = sphereComplementSlope z := by
      rw [overlapCholeskySlope, ha]
      simp [overlapColumnCross, K, sphereComplementSlope, mul_comm]
    simp only [overlapCholesky, sphereComplementFactor, ha, overlapCholeskySecond, hd,
      sphereComplementSecond, hc]
  rw [← he, overlapCholesky_mul_conjTranspose hK]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [overlapResidualMatrix, K, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.vecMulVec_apply]

theorem sphereComplementFactor_det_ne_zero {z : Signal 2} (hz : signalEnergy z < 1) :
    (sphereComplementFactor z).det ≠ 0 := by
  simp [sphereComplementFactor, Matrix.det_fin_two,
    (Real.sqrt_pos.mpr (sphereComplementFirst_pos hz)).ne',
    (Real.sqrt_pos.mpr (sphereComplementSecond_pos hz)).ne']

theorem sphereComplement_energy {z : Signal 2} (hz : signalEnergy z < 1)
    (w : Signal 2) :
    ellipticalEnergy (sphereComplementFirst z) (sphereComplementSecond z)
        (sphereComplementSlope z) w =
      signalEnergy w + Complex.normSq (star (z 0) * w 0 + star (z 1) * w 1) /
        sphereComplementDet z := by
  have ha := (sphereComplementFirst_pos hz).ne'
  have hd := (sphereComplementDet_pos hz).ne'
  unfold ellipticalEnergy sphereComplementSecond sphereComplementSlope
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.star_def, Complex.add_re, Complex.add_im]
  field_simp [ha, hd]
  simp [sphereComplementFirst, sphereComplementDet, signalEnergy, squaredEuclideanNorm,
    Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem overlapFrobeniusSq_matrixOfColumns (z w : Signal 2) :
    overlapFrobeniusSq (matrixOfColumns z w) = signalEnergy z + signalEnergy w := by
  simp [overlapFrobeniusSq, matrixOfColumns, signalEnergy, squaredEuclideanNorm,
    Fin.sum_univ_two]
  ring

theorem overlapDeterminant_matrixOfColumns {z : Signal 2} (hz : signalEnergy z < 1)
    (w : Signal 2) :
    overlapDeterminant (matrixOfColumns z w) = sphereComplementDet z *
      (1 - ellipticalEnergy (sphereComplementFirst z) (sphereComplementSecond z)
        (sphereComplementSlope z) w) := by
  rw [sphereComplement_energy hz, overlapDeterminant_identity,
    overlapFrobeniusSq_matrixOfColumns]
  field_simp [(sphereComplementDet_pos hz).ne']
  simp [sphereComplementDet, signalEnergy, squaredEuclideanNorm,
    Fin.sum_univ_two, matrixOfColumns, Matrix.det_fin_two, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

end RankOneSphereGeometry

section SequentialSphereLaw

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

instance (n : ℕ) : IsProbabilityMeasure (sphereProjectionLaw n) := by
  let : IsProbabilityMeasure (gammaMeasure (n + 1) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) zero_lt_one
  rw [← normalizedGaussianHead_law n]
  exact Measure.isProbabilityMeasure_map measurable_normalizedGaussianHead.aemeasurable

theorem ae_sphereProjectionLaw_energy (n : ℕ) :
    ∀ᵐ z ∂sphereProjectionLaw n, signalEnergy z < 1 := by
  rw [sphereProjectionLaw_eq_density]
  apply (ae_withDensity_iff (measurable_sphereLebesgueDensity n).ennreal_ofReal).mpr
  filter_upwards with z hz
  by_contra h
  simp [sphereLebesgueDensity, h] at hz

theorem ae_sourceHaarFirstTwoCoordinates_energy {m : ℕ} (hm : 3 ≤ m) :
    ∀ᵐ U ∂sourceUnitaryLaw m,
      signalEnergy (sourceHaarFirstTwoCoordinates (by lia) U) < 1 := by
  have h := ae_sphereProjectionLaw_energy (m - 3)
  rw [← sourceHaarFirstTwoCoordinates_law hm] at h
  exact (ae_map_iff (continuous_sourceHaarFirstTwoCoordinates _).measurable.aemeasurable
    (measurableSet_lt (by
      apply Continuous.measurable
      unfold signalEnergy squaredEuclideanNorm
      fun_prop) measurable_const)).mp h

@[fun_prop]
theorem measurable_sphereComplementFactor : Measurable sphereComplementFactor := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [sphereComplementFactor, sphereComplementSlope, sphereComplementSecond,
      sphereComplementDet, sphereComplementFirst, signalEnergy, squaredEuclideanNorm,
      Matrix.of_apply]
    fun_prop

def sequentialSphereMap (p : Signal 2 × Signal 2) : SourceOverlapMatrix :=
  matrixOfColumns p.1 (sphereComplementFactor p.1 *ᵥ p.2)

@[fun_prop]
theorem measurable_sequentialSphereMap : Measurable sequentialSphereMap := by
  unfold sequentialSphereMap
  have hmul : Continuous (fun p : SourceOverlapMatrix × Signal 2 ↦ p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  exact continuous_matrixOfColumns.measurable.comp (measurable_fst.prodMk
    (hmul.measurable.comp
      ((measurable_sphereComplementFactor.comp measurable_fst).prodMk measurable_snd)))

theorem lintegral_sourceHaarCorner_spheres {n : ℕ} (hn : 3 ≤ n)
    (f : SourceOverlapMatrix → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ U : SourceUnitary (n + 1), f (sourceHaarCorner (by lia) U) ∂sourceUnitaryLaw (n + 1)) =
      ∫⁻ z, ∫⁻ w, f (sequentialSphereMap (z, w))
        ∂sphereProjectionLaw (n - 3) ∂sphereProjectionLaw (n - 2) := by
  rw [lintegral_sourceHaarCorner_conditioning (by lia) f hf]
  have he :
      (∫⁻ U : SourceUnitary (n + 1), ∫⁻ x : Signal n,
        f (matrixOfColumns (sourceHaarFirstTwoCoordinates (by lia) U)
          (sourceComplementRows (by lia) U *ᵥ normalizedComplexVector x))
        ∂standardComplexGaussianTail n ∂sourceUnitaryLaw (n + 1)) =
      ∫⁻ U : SourceUnitary (n + 1), ∫⁻ w,
        f (sequentialSphereMap (sourceHaarFirstTwoCoordinates (by lia) U, w))
        ∂sphereProjectionLaw (n - 3) ∂sourceUnitaryLaw (n + 1) := by
    apply lintegral_congr_ae
    filter_upwards [ae_sourceHaarFirstTwoCoordinates_energy (by lia : 3 ≤ n + 1)] with U hU
    let z := sourceHaarFirstTwoCoordinates (by lia : 2 ≤ n + 1) U
    have hfv : Measurable (fun w : Signal 2 ↦ f (matrixOfColumns z w)) :=
      hf.comp (continuous_matrixOfColumns.measurable.comp (measurable_const.prodMk measurable_id))
    have hc : (standardComplexGaussianTail n).map
        (fun x ↦ sourceComplementRows (by lia) U *ᵥ normalizedComplexVector x) =
        (sphereProjectionLaw (n - 3)).map (fun w ↦ sphereComplementFactor z *ᵥ w) :=
      normalizedGaussian_projection_of_factor hn _ _ (sphereComplementFactor_det_ne_zero hU)
        ((sourceComplementRows_gram (by lia) U).trans (sphereComplementFactor_gram hU).symm)
    have hmul : Continuous (fun v : Signal n ↦ sourceComplementRows (by lia) U *ᵥ v) :=
      continuous_const.matrix_mulVec continuous_id
    have hi := congrArg (fun μ : Measure (Signal 2) ↦ ∫⁻ w, f (matrixOfColumns z w) ∂μ) hc
    rw [lintegral_map hfv (show Measurable (fun x : Signal n ↦
        sourceComplementRows (by lia) U *ᵥ normalizedComplexVector x) from
          hmul.measurable.comp (measurable_normalizedComplexVector n)),
      lintegral_map hfv (show Measurable (fun w ↦ sphereComplementFactor z *ᵥ w) by
        apply Continuous.measurable; fun_prop)] at hi
    exact hi
  rw [he]
  have hg : Measurable (fun z : Signal 2 ↦ ∫⁻ w,
      f (sequentialSphereMap (z, w)) ∂sphereProjectionLaw (n - 3)) :=
    (show Measurable (Function.uncurry (fun z w : Signal 2 ↦
      f (sequentialSphereMap (z, w)))) from hf.comp measurable_sequentialSphereMap).lintegral_prod_right
  rw [← lintegral_map hg (continuous_sourceHaarFirstTwoCoordinates _).measurable,
    sourceHaarFirstTwoCoordinates_law (by lia : 3 ≤ n + 1)]
  have he' : n + 1 - 3 = n - 2 := by lia
  rw [he']

theorem sourceOverlapLaw_eq_sequentialSpheres {n : ℕ} (hn : 3 ≤ n) :
    sourceOverlapLaw (n + 1) (by lia) =
      ((sphereProjectionLaw (n - 2)).prod (sphereProjectionLaw (n - 3))).map sequentialSphereMap := by
  rw [sourceOverlapLaw_eq_haarCorner]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (continuous_sourceHaarCorner _).measurable,
    lintegral_map hf measurable_sequentialSphereMap,
    lintegral_prod (fun p : Signal 2 × Signal 2 ↦ f (sequentialSphereMap p))
      (hf.comp measurable_sequentialSphereMap).aemeasurable]
  exact lintegral_sourceHaarCorner_spheres hn f hf

end SequentialSphereLaw

end NLA.FR05
