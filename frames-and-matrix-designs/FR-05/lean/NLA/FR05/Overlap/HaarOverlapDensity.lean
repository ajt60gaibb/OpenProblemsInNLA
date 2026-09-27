import NLA.FR05.Overlap.RankOneSphereGeometry
import NLA.FR05.Overlap.OverlapGaussian

/-!
# Haar overlap densities and the Lebesgue-Gaussian conversion

The sections develop `OverlapDensityAlgebra`, `HaarOverlapDensity`, `OverlapLebesgueGaussian`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section OverlapDensityAlgebra

open MeasureTheory Matrix
open scoped ENNReal

theorem overlapOperatorNorm_matrixOfColumns_lt_one_iff (z w : Signal 2) :
    overlapOperatorNorm (matrixOfColumns z w) < 1 ↔ signalEnergy z < 1 ∧
      ellipticalEnergy (sphereComplementFirst z) (sphereComplementSecond z)
        (sphereComplementSlope z) w < 1 := by
  constructor
  · intro hK
    have hc := overlapColumnEnergy_le (matrixOfColumns z w) 0
    have he : overlapColumnEnergy (matrixOfColumns z w) 0 = signalEnergy z := by
      simp [overlapColumnEnergy, matrixOfColumns, signalEnergy, squaredEuclideanNorm,
        Fin.sum_univ_two]
    rw [he] at hc
    have hz : signalEnergy z < 1 := by
      nlinarith [overlapOperatorNorm_nonneg (matrixOfColumns z w)]
    refine ⟨hz, ?_⟩
    have hd := overlapDeterminant_pos hK
    rw [overlapDeterminant_matrixOfColumns hz] at hd
    exact sub_pos.mp ((mul_pos_iff_of_pos_left (sphereComplementDet_pos hz)).mp hd)
  · rintro ⟨hz, hw⟩
    rw [overlapOperatorNorm_lt_one_iff, overlapFrobeniusSq_matrixOfColumns,
      overlapDeterminant_matrixOfColumns hz]
    have hwe : signalEnergy w < 1 := by
      rw [sphereComplement_energy hz] at hw
      have hp := div_nonneg
        (Complex.normSq_nonneg (star (z 0) * w 0 + star (z 1) * w 1))
        (sphereComplementDet_pos hz).le
      linarith
    exact ⟨by linarith, mul_pos (sphereComplementDet_pos hz) (sub_pos.mpr hw)⟩

def haarOverlapDensity (n : ℕ) (K : SourceOverlapMatrix) : ℝ :=
  if overlapOperatorNorm K < 1 then
    ((n + 3) * (n + 2) ^ 2 * (n + 1) : ℝ) / Real.pi ^ 4 * overlapDeterminant K ^ n else 0

theorem column_sphere_densities_product (n : ℕ) {z : Signal 2}
    (hz : signalEnergy z < 1) (w : Signal 2) :
    sphereLebesgueDensity (n + 1) z *
      ellipticalSphereDensity n (sphereComplementFirst z) (sphereComplementSecond z)
        (sphereComplementSlope z) w =
      haarOverlapDensity n (matrixOfColumns z w) := by
  unfold sphereLebesgueDensity ellipticalSphereDensity haarOverlapDensity
  rw [if_pos hz]
  simp only [overlapOperatorNorm_matrixOfColumns_lt_one_iff, hz, true_and]
  split_ifs with hw
  · rw [overlapDeterminant_matrixOfColumns hz]
    unfold sphereComplementSecond
    change ((↑(n + 1) + 1) * (↑(n + 1) + 2) / Real.pi ^ 2 *
      sphereComplementDet z ^ (n + 1)) *
      (((↑n + 1) * (↑n + 2)) /
        (Real.pi ^ 2 * sphereComplementFirst z * (sphereComplementDet z / sphereComplementFirst z)) *
          (1 - ellipticalEnergy (sphereComplementFirst z)
            (sphereComplementDet z / sphereComplementFirst z) (sphereComplementSlope z) w) ^ n) = _
    simp only [Nat.cast_add, Nat.cast_one, pow_succ, mul_pow]
    field_simp [(sphereComplementFirst_pos hz).ne', (sphereComplementDet_pos hz).ne',
      Real.pi_ne_zero]
    ring
  · ring

theorem haarOverlapDensity_eq_zero_of_firstColumn {z : Signal 2}
    (hz : ¬signalEnergy z < 1) (n : ℕ) (w : Signal 2) :
    haarOverlapDensity n (matrixOfColumns z w) = 0 := by
  unfold haarOverlapDensity
  rw [if_neg]
  exact fun h ↦ hz ((overlapOperatorNorm_matrixOfColumns_lt_one_iff z w).mp h).1

end OverlapDensityAlgebra

section HaarOverlapDensity

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

@[fun_prop]
theorem continuous_overlapFrobeniusSq : Continuous overlapFrobeniusSq := by
  unfold overlapFrobeniusSq
  fun_prop

@[fun_prop]
theorem continuous_overlapDeterminant : Continuous overlapDeterminant := by
  unfold overlapDeterminant
  fun_prop

theorem measurableSet_overlapOperatorNorm_lt_one :
    MeasurableSet {K : SourceOverlapMatrix | overlapOperatorNorm K < 1} := by
  simp_rw [overlapOperatorNorm_lt_one_iff]
  exact (measurableSet_lt continuous_overlapFrobeniusSq.measurable measurable_const).inter
    (measurableSet_lt measurable_const continuous_overlapDeterminant.measurable)

@[fun_prop]
theorem measurable_haarOverlapDensity (n : ℕ) : Measurable (haarOverlapDensity n) := by
  unfold haarOverlapDensity
  exact Measurable.ite measurableSet_overlapOperatorNorm_lt_one (by fun_prop) measurable_const

theorem sphereLebesgueDensity_nonneg (n : ℕ) (z : Signal 2) :
    0 ≤ sphereLebesgueDensity n z := by
  unfold sphereLebesgueDensity
  split_ifs with h <;> positivity

theorem sourceOverlapLaw_eq_density (n : ℕ) :
    sourceOverlapLaw (n + 4) (by lia) =
      volume.withDensity (fun K ↦ ENNReal.ofReal (haarOverlapDensity n K)) := by
  have h := sourceOverlapLaw_eq_sequentialSpheres (n := n + 3) (by lia)
  rw [show n + 3 - 2 = n + 1 by lia, show n + 3 - 3 = n by lia] at h
  rw [h]
  apply Measure.ext_of_lintegral
  intro f hf
  have hg : Measurable (fun z : Signal 2 ↦ ∫⁻ w,
      f (sequentialSphereMap (z, w)) ∂sphereProjectionLaw n) :=
    (show Measurable (Function.uncurry (fun z w : Signal 2 ↦
      f (sequentialSphereMap (z, w)))) from hf.comp measurable_sequentialSphereMap).lintegral_prod_right
  rw [lintegral_map hf measurable_sequentialSphereMap,
    lintegral_prod (fun p : Signal 2 × Signal 2 ↦ f (sequentialSphereMap p))
      (hf.comp measurable_sequentialSphereMap).aemeasurable,
    sphereProjectionLaw_eq_density (n + 1),
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_sphereLebesgueDensity (n + 1)).ennreal_ofReal hg,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_haarOverlapDensity n).ennreal_ofReal hf,
    lintegral_overlapMatrix_columns _ (by fun_prop)]
  simp only [Pi.mul_apply]
  apply lintegral_congr
  intro z
  by_cases hz : signalEnergy z < 1
  · have hfv : Measurable (fun w : Signal 2 ↦ f (matrixOfColumns z w)) :=
      hf.comp (continuous_matrixOfColumns.measurable.comp (measurable_const.prodMk measurable_id))
    have he := congrArg (fun μ : Measure (Signal 2) ↦ ∫⁻ w, f (matrixOfColumns z w) ∂μ)
      (sphereProjectionLaw_map_triangular n (sphereComplementFirst_pos hz)
        (sphereComplementSecond_pos hz) (sphereComplementSlope z))
    rw [lintegral_map hfv (by unfold triangularGaussian; fun_prop),
      lintegral_withDensity_eq_lintegral_mul _
        (measurable_ellipticalSphereDensity n _ _ _).ennreal_ofReal hfv] at he
    simp only [← sphereComplementFactor_mulVec] at he
    change ENNReal.ofReal (sphereLebesgueDensity (n + 1) z) *
      (∫⁻ w, f (matrixOfColumns z (sphereComplementFactor z *ᵥ w)) ∂sphereProjectionLaw n) = _
    rw [he, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro w
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (sphereLebesgueDensity_nonneg (n + 1) z),
      column_sphere_densities_product n hz]
  · simp only [sphereLebesgueDensity, if_neg hz, ENNReal.ofReal_zero, zero_mul]
    simp_rw [haarOverlapDensity_eq_zero_of_firstColumn hz n, ENNReal.ofReal_zero,
      zero_mul, lintegral_zero]

def sourceOverlapLebesgueDensity (M : ℕ) (K : SourceOverlapMatrix) : ℝ :=
  if overlapOperatorNorm K < 1 then
    (((M : ℝ) - 1) * ((M : ℝ) - 2) ^ 2 * ((M : ℝ) - 3)) / Real.pi ^ 4 *
      overlapDeterminant K ^ (M - 4) else 0

/-- The density of the overlap of two independent complex Haar two-frames. -/
theorem lemma_3_5 {M : ℕ} (hM : 4 ≤ M) :
    sourceOverlapLaw M (by lia) =
      volume.withDensity (fun K ↦ ENNReal.ofReal (sourceOverlapLebesgueDensity M K)) := by
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 4 := ⟨M - 4, by lia⟩
  rw [sourceOverlapLaw_eq_density]
  congr 1
  funext K
  congr 1
  unfold haarOverlapDensity sourceOverlapLebesgueDensity
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat]
  split_ifs <;> ring

end HaarOverlapDensity

section OverlapLebesgueGaussian

open MeasureTheory Matrix WithLp
open scoped BigOperators

def twoFlatten (n : ℕ) : (Fin 2 → Fin n → ℝ) ≃ᵐ (Fin (n + n) → ℝ) :=
  (MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ Fin n → ℝ)).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n ↦ ℝ)).symm.trans
      (MeasurableEquiv.arrowCongr' finSumFinEquiv (MeasurableEquiv.refl ℝ)))

theorem volumePreserving_twoFlatten (n : ℕ) : MeasurePreserving (twoFlatten n) :=
  (volume_preserving_arrowCongr' finSumFinEquiv (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id volume)).comp
    ((volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin n ↦ ℝ)).comp
      (volume_preserving_piFinTwo (fun _ : Fin 2 ↦ Fin n → ℝ)))

theorem sum_sq_twoFlatten (n : ℕ) (x : Fin 2 → Fin n → ℝ) :
    ∑ i, twoFlatten n x i ^ 2 = ∑ j, ∑ k, x j k ^ 2 := by
  change (∑ i, (Sum.elim (x 0) (x 1) (finSumFinEquiv.symm i)) ^ 2) = _
  rw [← (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).sum_comp]
  simp [Fin.sum_univ_two, Fintype.sum_sum_type]

def complexPairRealCoordinates : Signal 2 ≃ᵐ (Fin 4 → ℝ) :=
  (MeasurableEquiv.piCongrRight (fun _ : Fin 2 ↦ Complex.measurableEquivPi)).trans
    (twoFlatten 2)

theorem volumePreserving_complexPairRealCoordinates :
    MeasurePreserving complexPairRealCoordinates :=
  (volumePreserving_twoFlatten 2).comp
    (volume_preserving_pi (fun _ : Fin 2 ↦ Complex.volume_preserving_equiv_pi))

theorem sum_sq_complexPairRealCoordinates (z : Signal 2) :
    ∑ i, complexPairRealCoordinates z i ^ 2 = signalEnergy z := by
  change (∑ i, twoFlatten 2 (fun j ↦ Complex.measurableEquivPi (z j)) i ^ 2) = _
  have h := sum_sq_twoFlatten 2 (fun j ↦ Complex.measurableEquivPi (z j))
  calc
    _ = ∑ j, ∑ k, Complex.measurableEquivPi (z j) k ^ 2 := h
    _ = _ := by
      simp [signalEnergy, squaredEuclideanNorm, Fin.sum_univ_two, Complex.normSq_apply]
      ring

def overlapRealCoordinates : SourceOverlapMatrix ≃ᵐ OverlapCoordinates :=
  ((MeasurableEquiv.piCongrRight (fun _ : Fin 2 ↦ complexPairRealCoordinates)).trans
    (twoFlatten 4)).trans (EuclideanSpace.equiv (Fin 8) ℝ).symm.toHomeomorph.toMeasurableEquiv

theorem volumePreserving_overlapRealCoordinates :
    MeasurePreserving overlapRealCoordinates :=
  (PiLp.volume_preserving_toLp (Fin 8)).comp
    ((volumePreserving_twoFlatten 4).comp
      (volume_preserving_pi (fun _ : Fin 2 ↦ volumePreserving_complexPairRealCoordinates)))

theorem overlapRealCoordinates_norm_sq (K : SourceOverlapMatrix) :
    ‖overlapRealCoordinates K‖ ^ 2 = overlapFrobeniusSq K := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ i, ‖twoFlatten 4 (fun j ↦ complexPairRealCoordinates (K j)) i‖ ^ 2) = _
  simp_rw [Real.norm_eq_abs, sq_abs]
  rw [sum_sq_twoFlatten]
  simp_rw [sum_sq_complexPairRealCoordinates]
  rfl

theorem integrable_matrix_gaussian {c : ℝ} (hc : 0 < c) :
    Integrable (fun K : SourceOverlapMatrix ↦ Real.exp (-c * overlapFrobeniusSq K)) := by
  simpa only [Function.comp_def, overlapRealCoordinates_norm_sq] using
    (volumePreserving_overlapRealCoordinates.integrable_comp
      (by fun_prop : AEStronglyMeasurable (fun x : OverlapCoordinates ↦
        Real.exp (-c * ‖x‖ ^ 2)) volume)).mpr (integrable_overlap_gaussian hc)

theorem integrable_matrix_quartic_gaussian {c : ℝ} (hc : 0 < c) :
    Integrable (fun K : SourceOverlapMatrix ↦ overlapFrobeniusSq K ^ 2 *
      Real.exp (-c * overlapFrobeniusSq K)) := by
  have h := (volumePreserving_overlapRealCoordinates.integrable_comp
    (by fun_prop : AEStronglyMeasurable (fun x : OverlapCoordinates ↦
      ‖x‖ ^ 4 * Real.exp (-c * ‖x‖ ^ 2)) volume)).mpr
      (integrable_overlap_quartic_gaussian hc)
  simpa only [Function.comp_def, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
    overlapRealCoordinates_norm_sq] using h

theorem matrix_local_integral_scale (c : ℝ) {m : ℝ} (hm : 0 < m) :
    m ^ 5 * (∫ K : SourceOverlapMatrix, overlapFrobeniusSq K ^ 2 *
      Real.exp (-c * m * overlapFrobeniusSq K)) =
        (∫ K : SourceOverlapMatrix, overlapFrobeniusSq K ^ 2 *
          Real.exp (-c * overlapFrobeniusSq K)) / m := by
  have he (a : ℝ) :
      (∫ K : SourceOverlapMatrix, overlapFrobeniusSq K ^ 2 * Real.exp (-a * overlapFrobeniusSq K)) =
      ∫ x : OverlapCoordinates, ‖x‖ ^ 4 * Real.exp (-a * ‖x‖ ^ 2) := by
    convert volumePreserving_overlapRealCoordinates.integral_comp
      overlapRealCoordinates.measurableEmbedding (fun x ↦ ‖x‖ ^ 4 * Real.exp (-a * ‖x‖ ^ 2)) using 1
    simp only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, overlapRealCoordinates_norm_sq]
  simp_rw [show -c * m = -(c * m) by ring]
  rw [he, he]
  simpa only [neg_mul] using overlap_local_integral_scale c hm

end OverlapLebesgueGaussian

end NLA.FR05
